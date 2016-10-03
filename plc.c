/*
 * PLM-1 power line controller kernel driver By DAVID WANG
 *
 * Copyright (C) 2015,2016  Morgan Solar Inc
 * Author:	David Wang <david.wang@morgansolar.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 */

#include <linux/init.h>
#include <linux/module.h>
#include <linux/device.h>
#include <linux/kernel.h>
#include <linux/interrupt.h>
#include <linux/fs.h>
#include <linux/sysfs.h>
#include <linux/delay.h>
#include <linux/spi/spi.h>
#include <linux/irq.h>
#include <linux/gpio.h>
#include <linux/wait.h>
#include <linux/spinlock.h>
#include <linux/slab.h>
#include <asm/uaccess.h>
#include <asm/atomic.h>
#include <linux/cdev.h>
#include <linux/types.h>        /* size_t */
#include <linux/proc_fs.h>
#include <linux/poll.h>
#include <linux/fcntl.h>        /* O_ACCMODE */
#include <linux/bitops.h>
#include <linux/plc.h>         /* local definitions */

MODULE_LICENSE("GPL");
MODULE_AUTHOR("DAVIDWANG");
MODULE_DESCRIPTION("PLM-1 PLC kernel driver");
MODULE_VERSION("1.0");

//#define PLC_DEBUG
#define PLC_TX_DEBUG

// PLC interrupt name for the GPIO 0_6 pin interrupt
#define GPIO6_INT_NAME  "plc_int"
#define SPI_MODE_USE	SPI_MODE_1
#define BIT_PER_WORD    8

// Defines PLC input control codes
# define CCR     0x0A  // Control character (first nibble of a packet)
# define DISR    0x12  // Disables receiver
# define SBQ     0x13  // Sets busy queue
# define RESET   0x16  // Resets PLM-1
# define NOP     0x1F  // No operation

// Defines PLC output control codes
# define SOP     0x0A  //define packet header here
# define EOD     0x10  // End of field
# define EOP     0x11  // End of packet
# define ERR     0x12  // Error received
# define ROVR    0x13  // Receiver over-run
# define COLL    0x14  // Collision
# define NORES   0x15  // No response
# define P2LONG  0x16  // Packet is too long
# define TUNR    0x17  // Transmitter under-run
# define TXRE    0x18  // Transmitter register is empty
# define TOVR    0x19  // Transmitter over-run

// this is used to calculate device pin value from the GPIO pin value
#define GPIO_TO_PIN(bank, gpio)    (32 * (bank) + (gpio))

// GPIO pin 3_17 of debug LED
#define DEBUG_LED        GPIO_TO_PIN(2, 0)
//GPIO pin2_22 PLC_RST
#define PLC_RST          GPIO_TO_PIN(2, 22)
//GPIO pin0_6 PLC_INT
#define PLC_INT          GPIO_TO_PIN(2, 23)
//GPIO pin2_24 PLC CONFIG
#define PLC_CNF          GPIO_TO_PIN(2, 24)

//GPIO1_8, output, set to low to disable RX to PLM
#define GPIO_RX_SWITCH        GPIO_TO_PIN(1, 8)
// macros for disable/enable RX to PLM
#define GPIO_DISABLE_RX  gpio_set_value(GPIO_RX_SWITCH, 255)
#define GPIO_ENABLE_RX   gpio_set_value(GPIO_RX_SWITCH, 0)


// macros for turning the LEDs on and off
#define DEBUG_LED_ON     gpio_set_value(DEBUG_LED, 255)
#define DEBUG_LED_OFF    gpio_set_value(DEBUG_LED, 0)
#define PLC_RST_HI       gpio_set_value(PLC_RST, 255)
#define PLC_RST_LO       gpio_set_value(PLC_RST, 0)
#define reset_plc()      {PLC_RST_LO; \
                         udelay(500); \
                         PLC_RST_HI;  \
                         udelay(100);   \
                         }
#define is_plc_cnfed()   gpio_get_value(PLC_CNF)

#define SPI_MODE_MASK		(SPI_CPHA | SPI_CPOL | SPI_CS_HIGH \
				| SPI_LSB_FIRST | SPI_3WIRE | SPI_LOOP \
				| SPI_NO_CS | SPI_READY)

#define BUF_SIZE            127

typedef enum {FALSE=0, TRUE=1} BOOL;
typedef enum {w=0,r=1,o=3} BUF_ATTR;
typedef enum {TX, RX} PLC_STATUS;

struct plcdev_data {
	dev_t			             devt;
	struct spi_device            *spi;
	spinlock_t                   spi_lock;
	wait_queue_head_t            plc_wait_queue;

	struct spi_transfer          tr;
	struct spi_message           m;
	struct workqueue_struct      *plc_tx_wq;
    struct work_struct           plc_tx_packet;
    struct completion            done;

	/* buffer is NULL unless this device is open (users > 0) */
	struct mutex		         buf_lock;
	unsigned		             users;
	u8			                 *buffer;
	u8                           *rxbuf;//cause extra memcpy?
	u8                           rxtemp;
	volatile int                 rxcount;
	volatile int                 txindex;
	volatile BOOL                TX_InProgress;
	volatile BOOL                RX_InProgress;
	volatile BOOL                RX_Complete;
	volatile BOOL                TX_Complete;
	u8                           count;
    struct cdev                  cdev;
    BUF_ATTR                     bufattr;
    volatile unsigned long       tx_attemp;//for statistics only
    volatile unsigned long       tx_count;//for statistics only

    PLC_STATUS                   plc_status;
    volatile int                 rxor;//rx overrun counter
    volatile int                 txretry;

};

static struct class *plcdev_class;

static volatile long int    gpio_pin_flags ;//bit0:DEBUG_LED ; bit1:PLC_RST
                                           //bit2:PLC_INT ; bit3:PLC_CNF
int plc_major =   PLC_MAJOR;
int plc_minor =   0;
int plc_nr_devs = PLC_NR_DEVS; /* number of bare plcdev devices */
static volatile int CS_CHANGE = 1;//default value ; can be change by using ioctl() system call
static volatile int SPI_BITS = 8;//default value ; can be change by using ioctl() system call
static volatile int TR_DELAY = 5;//default value ; can be change by using ioctl() system call
static volatile int SPI_SPEED_USE = 1125000;//default value ; can be change by using ioctl() system call
static const u8     varNOP = NOP;
static const int    max_retry = 100;
static const int    int_timeout = 50;

/********function declarations*****************************/
static int spi_asyncput(struct plcdev_data *plcdev, u8 *txbuf);
static int spi_syncput(struct plcdev_data *plcdev, u8 *txbuf, u8 *rxbuf);
static int   plc_init(void);
static void  plc_exit(void);static void exit_plc(void);
static void plc_setup_cdev(struct plcdev_data *dev, int index);
static int plc_open(struct inode *, struct file *);
static int plc_close(struct inode *, struct file *);
static ssize_t plc_read(struct file *, char *, size_t, loff_t *);
static ssize_t plc_write(struct file *, const char *, size_t, loff_t *);
static unsigned int plc_poll(struct file *filp, poll_table *wait);
static long plc_ioctl(struct file *filp, unsigned int cmd, unsigned long arg);
static irqreturn_t plc_interrupt_handler(int irq, void *dev_id);
static ssize_t plc_send_packet(struct plcdev_data *plc_dev, size_t count);
//static BOOL plc_send_byte(struct plcdev_data *plc_dev ,size_t index);
static irqreturn_t plc_rx_wq_handler(int irq, void *dev_id);
static void plc_tx_wq_handler(struct work_struct *work);
static ssize_t plc_kobject_read(struct file *filp, struct kobject *kobj,
		  struct bin_attribute *attr,
		  char *buf, loff_t off, size_t size);
static ssize_t plc_kobject_show (struct device *d,
		 struct device_attribute *attr, const char *buf, size_t count);
static ssize_t plc_rxoverrun_show (struct device *d,
		 struct device_attribute *attr, const char *buf, size_t count);
static void spidev_complete(void *arg);
static __inline void handle_tx_error(struct plcdev_data *plc_dev);

/**************************************************************/
static int spi_asyncput(struct plcdev_data *plcdev, u8 *txbuf)
{
	int status = 0;

	    spi_message_init(&plcdev->m);

	    plcdev->tr.tx_buf = txbuf;
	    plcdev->tr.rx_buf = &(plcdev->rxtemp);
	    plcdev->m.complete = spidev_complete;
	    plcdev->m.context = &plcdev->done;

	spi_message_add_tail(&plcdev->tr, &plcdev->m);

	status = spi_async(plcdev->spi, &plcdev->m);

#ifdef PLC_DEBUG
	printk(KERN_INFO "spi_asyncput status=%x tx=%x spi=%x\n",status,*txbuf,plcdev->spi);
#endif

	return status;
}


#if 0
static int spi_syncput(struct plcdev_data *plcdev, u8 *txbuf, u8 *rxbuf)
{
	//struct spi_transfer tr;
	//struct spi_message m;
    int status = 0;
   //unsigned long flags;

    /*u8 dummyBuf[64];
    u8 tmpTxBuf[64];
    u8 tmpRxBuf[64];*/

    plcdev->spi_sync_tx_byte[0] = txbuf[0];
    plcdev->spi_sync_rx_byte[0] = rxbuf[0];

	spi_message_init(&plcdev->tx_m);
   plcdev->tx_m.is_dma_mapped = FALSE;
   memset(&plcdev->tx_tr, 0, sizeof(plcdev->tx_tr));

	plcdev->tx_tr.tx_buf = &(plcdev->spi_sync_tx_byte[0]);
	plcdev->tx_tr.rx_buf = &(plcdev->spi_sync_rx_byte[0]);
	plcdev->tx_tr.cs_change = CS_CHANGE;
	plcdev->tx_tr.delay_usecs = TR_DELAY ;
	plcdev->tx_tr.speed_hz = SPI_SPEED_USE;
	plcdev->tx_tr.bits_per_word = SPI_BITS;
	plcdev->tx_tr.len = 1;

	spi_message_add_tail(&plcdev->tx_tr, &plcdev->tx_m);

	status = spi_sync(plcdev->spi, &plcdev->tx_m);

//#ifdef PLC_DEBUG
	printk(KERN_ERR "spi_syncput status=%x, tx:[0x%x], rx:[0x%x] \n",status,txbuf[0],rxbuf[0]);
//#endif

	return status;
}
#else
static int spi_syncput(struct plcdev_data *plcdev, u8 *txbuf, u8 *rxbuf)
{
    int status = 0;
    struct spi_transfer tr;
    struct spi_message m;
  
    u8      *local_buf;

    local_buf = kmalloc(2/*SPI_BUFSIZ*/, GFP_KERNEL);  
    if (!local_buf)  
         return -ENOMEM;  

   local_buf[0] = txbuf[0];

   spi_message_init(&m);

   //m.is_dma_mapped = FALSE;
   memset(&tr, 0, sizeof(tr));

   tr.tx_buf        = (const void *)local_buf;
   tr.rx_buf        = (void *)(&local_buf[1]);
   tr.cs_change     = CS_CHANGE;
   tr.delay_usecs   = 10/*TR_DELAY*/ ;
   tr.speed_hz      = SPI_SPEED_USE;
   tr.bits_per_word = SPI_BITS;
   tr.len           = 1;

   tr.tx_nbits = SPI_NBITS_SINGLE;
   tr.rx_nbits = SPI_NBITS_SINGLE;

   spi_message_add_tail(&tr, &m);

   //spin_lock_irqsave(&spilock,spilockflag);
   status = spi_sync(plcdev->spi, &m);
   //spin_unlock_irqrestore(&spilock,spilockflag);

   if (status == 0)  
           rxbuf[0] = local_buf[1];  

    kfree(local_buf);

   //printk(KERN_ERR "spi_syncput - status:[%d],tx=%x, rx=%x \n",status,(int)txbuf[0], (int)rxbuf[0] );

   return status;
}



#endif

static ssize_t plc_send_packet(struct plcdev_data *plc_dev, size_t count)
{
	u8 i, temp = 0;
	int retry_counter = 0;
    ssize_t status = 0;

	plc_dev->RX_InProgress = FALSE;
	plc_dev->txretry = 0;

    if((plc_dev->buffer[0]>0x0F) || ((plc_dev->buffer[count-1]) != EOP))
    	return -EINVAL;
    for(i=1;i<(count-2);i++)
    	if(plc_dev->buffer[i]>EOD)
    	return -EINVAL;

    do{
    	if(spi_syncput(plc_dev, &plc_dev->buffer[0], &temp)){
    		if(retry_counter++ > max_retry)
    		       return -EAGAIN;
    	}
    	else retry_counter = 0;

    }while(temp != NOP);

    //plc_dev->TX_InProgress = TRUE;
    enable_irq(gpio_to_irq(PLC_INT));//start TXing
    //disable_irq(gpio_to_irq(PLC_INT));
    while(plc_dev->TX_Complete != TRUE){
    	//enable_irq(gpio_to_irq(PLC_INT));
        if(wait_event_interruptible(plc_dev->plc_wait_queue, (plc_dev->TX_Complete==TRUE))){
    	   	disable_irq(gpio_to_irq(PLC_INT));//balance int
    	   	return -ERESTARTSYS; /* signal: tell the fs layer to handle it */
    	 }
    }
#ifdef PLC_TX_DEBUG
    printk(KERN_INFO "write awaked\n");
#endif
    //disable_irq(gpio_to_irq(PLC_INT));
    if(plc_dev->count == 0)//tx success
    	status = count;
    else
    	status = -EAGAIN;
    plc_dev->TX_Complete= FALSE;

    return status;
}
static irqreturn_t plc_rx_wq_handler(int irq, void *dev_id)
{
  struct plcdev_data *plc_dev;
  int status;
  //int retry_counter = 0;

  plc_dev = dev_id;

  //printk(KERN_INFO "bottom enter\n");
  status = wait_for_completion_interruptible_timeout(&plc_dev->done, int_timeout);
  if(status<=0) return IRQ_HANDLED;

  status = plc_dev->m.status;

  if(!status){
  /* start of cto packet received? */
  if (plc_dev->RX_InProgress==FALSE)
  {
    /* store the message header when received */
     if((plc_dev->rxtemp&0xff) == SOP){
      /* indicate that a cto packet is being received */
    	 plc_dev->RX_InProgress = TRUE;
    	 plc_dev->rxbuf[0] = SOP;
      /*  packet data count */
      plc_dev->rxcount = 1;
      //plc_dev->bufattr = o;
      }

  }
  else
  {
    /* store the next packet byte */
    if((plc_dev->rxtemp&0xff) <= EOP ){
      plc_dev->rxbuf[plc_dev->rxcount] = plc_dev->rxtemp&0xff;
      /* increment the packet data count */
      plc_dev->rxcount++;
      if(plc_dev->rxcount > BUF_SIZE){
    	  plc_dev->RX_InProgress = FALSE;//error occurrence;abort packet received;
          /* reset packet data count */
    	  plc_dev->rxcount = 0;
    	  //mutex_unlock(&plc_dev->buf_lock);
#ifdef PLC_TX_DEBUG
    	  printk(KERN_ERR "rxbuffer overflows\n");
#endif
       }
      /* check to see if the entire packet was received */
      if (plc_dev->rxbuf[plc_dev->rxcount-1] == EOP)
      {
        /* done with packet reception */
    	 plc_dev->RX_InProgress = FALSE;
    	 mutex_lock(&plc_dev->buf_lock);
    	 if(plc_dev->RX_Complete == TRUE){
#ifdef PLC_TX_DEBUG
            printk(KERN_INFO "rx overrun\n");
#endif
            plc_dev->rxor++;
         }
    	 plc_dev->RX_Complete = TRUE;
    	 memcpy(plc_dev->buffer, plc_dev->rxbuf, plc_dev->rxcount);
    	 plc_dev->count = plc_dev->rxcount;
         plc_dev->bufattr = r;
#ifdef PLC_TX_DEBUG
     printk(KERN_INFO "rx complete and wakup read\n");
#endif
        mutex_unlock(&plc_dev->buf_lock);
    	 /* packet reception complete */
    	wake_up_interruptible(&plc_dev->plc_wait_queue);
    	//mutex_unlock(&plc_dev->buf_lock);
        //return IRQ_HANDLED;
      }
    }
      else {
       plc_dev->RX_InProgress = FALSE;//error occurrence;abort packet received;
        /* reset packet data count */
       //plc_dev->rxcount = 0;
#ifdef PLC_TX_DEBUG
     printk(KERN_ERR "rx error in middle@%x\n", plc_dev->rxtemp&0xff);
#endif
      }
    }
  }
  else
      plc_dev->RX_InProgress=FALSE;

  //printk(KERN_INFO "bottom exit\n");

  return IRQ_HANDLED;
}

static void plc_tx_wq_handler(struct work_struct *work)
{
	struct plcdev_data *plc_dev;
	u8 temp = 0;
	int retry_counter = 0;

	  if(!work)
		 return;

	  plc_dev = container_of(work, struct plcdev_data, plc_tx_packet);

	  if(plc_dev->plc_status == TX){
	 	  if(spi_syncput(plc_dev, (u8 *)(&varNOP), &temp)){
	 		  handle_tx_error(plc_dev);
	 	  }
	 	  else{
	 		  if((temp&0xff) != TXRE){
	 		   plc_dev->txindex = 0;
	 		  if((plc_dev->txretry++) > max_retry){
	 		 	   handle_tx_error(plc_dev);
	 		 	   return;
	 		  }
	 		   do{
	 			 spi_syncput(plc_dev, &plc_dev->buffer[0], &temp);
	 			 if(retry_counter++ > max_retry){
	 				handle_tx_error(plc_dev);
	 				return;
	 			}
	 		   }while(temp != NOP);
	 		  }
	 		  else{
	 		  if(plc_dev->txindex == 0){
	 			  plc_dev->tx_attemp++;
	 #ifdef PLC_TX_DEBUG
	 			  printk(KERN_INFO "tx begin@attemp%ld\n",plc_dev->tx_attemp);
	 #endif
	 		  }
	 		  if(plc_dev->buffer[plc_dev->txindex] == EOP){
	 			  disable_irq(gpio_to_irq(PLC_INT));
	 			  plc_dev->TX_Complete = TRUE;
	 			  plc_dev->plc_status = RX;
	 			  plc_dev->txindex = 0;
	 			  plc_dev->count = 0;//success
	 			  plc_dev->tx_count++;//for statistics only

	 #ifdef PLC_TX_DEBUG
	 	 printk(KERN_INFO "tx ending@attemp%ld\n",plc_dev->tx_attemp);
	 	 printk(KERN_INFO "wake up write\n");
	 #endif
	 			  wake_up_interruptible(&plc_dev->plc_wait_queue);
	 		  }
	 		  else{
	 			plc_dev->txindex++;
	 			if(spi_syncput(plc_dev, &plc_dev->buffer[plc_dev->txindex], &temp)){
	 				handle_tx_error(plc_dev);
	 				return;
	 			}
	 		   }
	 		  }
	 	  }
	   }
}

static __inline void handle_tx_error(struct plcdev_data *plc_dev)
{
	disable_irq(gpio_to_irq(PLC_INT));
	plc_dev->TX_InProgress = FALSE;
	plc_dev->TX_Complete = TRUE;
	plc_dev->plc_status = RX;
	plc_dev->txindex = 0;

#ifdef PLC_TX_DEBUG
	printk(KERN_ERR "spi_syncput failed\n");
#endif
	wake_up_interruptible(&plc_dev->plc_wait_queue);
}

static int plc_open(struct inode *inode, struct file *filp)
{
	int status=0;
	struct plcdev_data *plcdev;

	plcdev = container_of(inode->i_cdev, struct plcdev_data, cdev);
	if(plcdev == NULL){
		printk(KERN_ERR "failed to open plcdev!\n");
		return -EINVAL;
	}
	if(plcdev->users > 0) return -EBUSY;

	INIT_WORK(&plcdev->plc_tx_packet, plc_tx_wq_handler);
	// initializing workqueue
	plcdev->plc_tx_wq = alloc_workqueue("plc_tx_wq", WQ_HIGHPRI , 1);
	if(plcdev->plc_tx_wq == NULL){
		printk(KERN_ERR "failed to creat workqueue!\n");
		return -ENOMEM;
	}
	if (!plcdev->buffer) {
		  plcdev->buffer = kmalloc(BUF_SIZE , GFP_KERNEL);
		  if (!plcdev->buffer) {
			printk(KERN_ERR "no mem for plc buffer!\n");
			destroy_workqueue(plcdev->plc_tx_wq);
			return -ENOMEM;
		  }
	}
	if (!plcdev->rxbuf) {
		plcdev->rxbuf = kmalloc(BUF_SIZE , GFP_KERNEL);
		if (!plcdev->rxbuf) {
		  printk(KERN_ERR "no mem for plc buffer!\n");
		  destroy_workqueue(plcdev->plc_tx_wq);
		  kfree(plcdev->buffer);
		  return -ENOMEM;
	  }
	}

	init_waitqueue_head(&plcdev->plc_wait_queue);
	spi_message_init(&plcdev->m);
	init_completion(&plcdev->done);

	plcdev->tr.cs_change = CS_CHANGE;
	plcdev->tr.delay_usecs = TR_DELAY ;
	plcdev->tr.speed_hz = SPI_SPEED_USE;
	plcdev->tr.bits_per_word = SPI_BITS;
	plcdev->tr.len = 1;

	plcdev->m.complete = spidev_complete;
	plcdev->m.context = &plcdev->done;
	plcdev->TX_InProgress = FALSE;
	plcdev->RX_InProgress = FALSE;
    plcdev->RX_Complete =   FALSE;
    plcdev->TX_Complete =   FALSE;
    plcdev->tx_attemp = 0;
    plcdev->tx_count = 0;
    plcdev->txindex = 0;
    plcdev->rxor = 0;
    plcdev->plc_status = RX;

	plcdev->users++;
	filp->private_data = plcdev;

#ifdef PLC_DEBUG
	printk(KERN_INFO "plc_open and plc-spi dev found @0x%x\n", (int)(plcdev->spi));
#endif


	//status = request_irq(gpio_to_irq(PLC_INT), plc_interrupt_handler, IRQF_TRIGGER_RISING, GPIO6_INT_NAME, plcdev);
	status = request_threaded_irq(gpio_to_irq(PLC_INT), plc_interrupt_handler, plc_rx_wq_handler, IRQF_TRIGGER_RISING /*| IRQF_DISABLED*/, GPIO6_INT_NAME, plcdev);
	if (status) {
	   	printk(KERN_ERR "plc request IRQ fails!\n");
	   	destroy_workqueue(plcdev->plc_tx_wq);
	   	kfree(plcdev->buffer);
	   	kfree(plcdev->rxbuf);
	   	return status;
	}
	disable_irq(gpio_to_irq(PLC_INT));
#ifdef PLC_DEBUG
	printk(KERN_INFO "plc request IRQ success!!\n");
#endif

	return status;
}

static int plc_close(struct inode *inode, struct file *filp)
{
	struct plcdev_data *plcdev;

    plcdev = filp->private_data;
    free_irq(gpio_to_irq(PLC_INT), plcdev);
    filp->private_data = NULL;

#ifdef PLC_DEBUG
	printk(KERN_INFO "plc free IRQ success!!\n");
#endif
    if(!(plcdev->users--)){
    	int		dofree;
    	kfree(plcdev->buffer);
    	kfree(plcdev->rxbuf);
    	plcdev->buffer = NULL;
    	plcdev->rxbuf = NULL;
    	flush_workqueue(plcdev->plc_tx_wq);
    	destroy_workqueue(plcdev->plc_tx_wq);
    	spin_lock_irq(&plcdev->spi_lock);
    	dofree = (plcdev->spi == NULL);
    	spin_unlock_irq(&plcdev->spi_lock);

    	if (dofree)
    	  kfree(plcdev);
    }
    return 0;
}

static ssize_t plc_read(struct file *filp, char __user *buf, size_t count, loff_t *f_pos)
{
	struct plcdev_data	*plcdev;
	size_t			    status = 0;
    u8                  temp[BUF_SIZE];//auto!  we are safe!  no lock needed
    size_t              rxcount;//auto! we are safe!

        if(!is_plc_cnfed())
        	return -EIO;
		if (count > BUF_SIZE+1)
			return -EMSGSIZE;

		plcdev = filp->private_data;

		mutex_lock(&plcdev->buf_lock);
		while (plcdev->RX_Complete != TRUE) {
			mutex_unlock(&plcdev->buf_lock);
			//enable_irq(gpio_to_irq(PLC_INT));
			if (filp->f_flags & O_NONBLOCK)
	                  return -EAGAIN;
			if(wait_event_interruptible(plcdev->plc_wait_queue, (plcdev->RX_Complete==TRUE)))
						return -ERESTARTSYS; /* signal: tell the fs layer to handle it */;
			//disable_irq_nosync(gpio_to_irq(PLC_INT));
			mutex_lock(&plcdev->buf_lock);
		}
#ifdef PLC_TX_DEBUG
     printk(KERN_INFO "user reading\n");
#endif
		/*****ok , data is there*********/
		rxcount = plcdev->count;
		memcpy(temp, plcdev->buffer, rxcount);
		plcdev->RX_Complete = FALSE;
		mutex_unlock(&plcdev->buf_lock);

		if (rxcount>2) {
			unsigned long	missing;

			missing = copy_to_user(buf, temp, rxcount);
			if (missing)
				status = -EFAULT;
			else
				status = rxcount;
		}
		else
			   status = -EINVAL;

#ifdef PLC_DEBUG
      printk(KERN_INFO "read waked by wq and status=%d\n",status);
#endif
		return status;
}

static ssize_t plc_write(struct file *filp, const char __user *buf,
		               size_t count, loff_t *f_pos)
{
	struct plcdev_data	*plcdev;
	ssize_t			status = 0;
	unsigned long	missing;

	if(!is_plc_cnfed())
	    return -EIO;
	if(count<=2 || count > BUF_SIZE)
		return -EMSGSIZE;

	plcdev = filp->private_data;

	disable_irq(gpio_to_irq(PLC_INT));
	mutex_lock(&plcdev->buf_lock);
	missing = copy_from_user(plcdev->buffer, buf, count);
	plcdev->count = count;
	plcdev->txindex = 0;
	plcdev->plc_status = TX;
	plcdev->RX_InProgress = FALSE;
	    if (missing == 0)
			status = plc_send_packet(plcdev, count);

	    else
			status = -EFAULT;
	plcdev->bufattr = w;
	plcdev->plc_status = RX;
	mutex_unlock(&plcdev->buf_lock);
	enable_irq(gpio_to_irq(PLC_INT));

	return status;
}

static unsigned int plc_poll(struct file *filp, poll_table *wait)
{
	    struct plcdev_data *dev = filp->private_data;
        unsigned int mask = 0;

        if(!is_plc_cnfed())
        	    return -EIO;
        poll_wait(filp, &dev->plc_wait_queue,  wait);
        mutex_lock(&dev->buf_lock);
        if (dev->RX_Complete==TRUE)
          mask |= POLLPRI;/* readable */
        mutex_unlock(&dev->buf_lock);
        return mask;
}

static void spidev_complete(void *arg)
{
	complete(arg);
}

static ssize_t
spidev_sync(struct plcdev_data *plcdev, struct spi_message *message)
{
	DECLARE_COMPLETION_ONSTACK(done);
	int status;

	message->complete = spidev_complete;
	message->context = &done;

	spin_lock_irq(&plcdev->spi_lock);
	if (plcdev->spi == NULL)
		status = -ESHUTDOWN;
	else
		status = spi_async(plcdev->spi, message);
	spin_unlock_irq(&plcdev->spi_lock);

	if (status == 0) {
		wait_for_completion(&done);
		status = message->status;
		if (status == 0)
			status = message->actual_length;
	}
	return status;
}

static int spidev_message(struct plcdev_data *plcdev,
		struct spi_ioc_transfer *u_xfers, unsigned n_xfers)
{
	struct spi_message	msg;
	struct spi_transfer	*k_xfers;
	struct spi_transfer	*k_tmp;
	struct spi_ioc_transfer *u_tmp;
	unsigned		n, total;
	u8			*buf;
	int			status = -EFAULT;

	spi_message_init(&msg);
	k_xfers = kcalloc(n_xfers, sizeof(*k_tmp), GFP_KERNEL);
	if (k_xfers == NULL)
		return -ENOMEM;

	/* Construct spi_message, copying any tx data to bounce buffer.
	 * We walk the array of user-provided transfers, using each one
	 * to initialize a kernel version of the same transfer.
	 */
	buf = plcdev->buffer;
	total = 0;
	for (n = n_xfers, k_tmp = k_xfers, u_tmp = u_xfers;
			n;
			n--, k_tmp++, u_tmp++) {
		k_tmp->len = u_tmp->len;

		total += k_tmp->len;
		if (total > BUF_SIZE) {
			status = -EMSGSIZE;
			goto done;
		}

		if (u_tmp->rx_buf) {
			k_tmp->rx_buf = buf;
			if (!access_ok(VERIFY_WRITE, (u8 __user *)
						(uintptr_t) u_tmp->rx_buf,
						u_tmp->len))
				goto done;
		}
		if (u_tmp->tx_buf) {
			k_tmp->tx_buf = buf;
			if (copy_from_user(buf, (const u8 __user *)
						(uintptr_t) u_tmp->tx_buf,
					u_tmp->len))
				goto done;
		}
		buf += k_tmp->len;

		k_tmp->cs_change = !!u_tmp->cs_change;
		k_tmp->bits_per_word = u_tmp->bits_per_word;
		k_tmp->delay_usecs = u_tmp->delay_usecs;
		k_tmp->speed_hz = u_tmp->speed_hz;
#ifdef VERBOSE
		dev_dbg(&spidev->spi->dev,
			"  xfer len %zd %s%s%s%dbits %u usec %uHz\n",
			u_tmp->len,
			u_tmp->rx_buf ? "rx " : "",
			u_tmp->tx_buf ? "tx " : "",
			u_tmp->cs_change ? "cs " : "",
			u_tmp->bits_per_word ? : spidev->spi->bits_per_word,
			u_tmp->delay_usecs,
			u_tmp->speed_hz ? : spidev->spi->max_speed_hz);
#endif
		spi_message_add_tail(k_tmp, &msg);
	}

	status = spidev_sync(plcdev, &msg);
	if (status < 0)
		goto done;

	/* copy any rx data out of bounce buffer */
	buf = plcdev->buffer;
	for (n = n_xfers, u_tmp = u_xfers; n; n--, u_tmp++) {
		if (u_tmp->rx_buf) {
			if (__copy_to_user((u8 __user *)
					(uintptr_t) u_tmp->rx_buf, buf,
					u_tmp->len)) {
				status = -EFAULT;
				goto done;
			}
		}
		buf += u_tmp->len;
	}
	status = total;

done:
	kfree(k_xfers);
	return status;
}

static long
plc_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
	int			err = 0;
	int			retval = 0;
	struct plcdev_data	*plcdev;
	struct spi_device	*spi;
	u32			tmp;
	unsigned		n_ioc;
	struct spi_ioc_transfer	*ioc;
	u8 tx_rate;

	/* Check type and command number */
	if (_IOC_TYPE(cmd) != SPI_IOC_MAGIC)
		return -ENOTTY;

	/* Check access direction once here; don't repeat below.
	 * IOC_DIR is from the user perspective, while access_ok is
	 * from the kernel perspective; so they look reversed.
	 */
	if (_IOC_DIR(cmd) & _IOC_READ)
		err = !access_ok(VERIFY_WRITE,
				(void __user *)arg, _IOC_SIZE(cmd));
	if (err == 0 && _IOC_DIR(cmd) & _IOC_WRITE)
		err = !access_ok(VERIFY_READ,
				(void __user *)arg, _IOC_SIZE(cmd));
	if (err)
		return -EFAULT;

	/* guard against device removal before, or while,
	 * we issue this ioctl.
	 */
	plcdev = filp->private_data;
	spin_lock_irq(&plcdev->spi_lock);
	spi = spi_dev_get(plcdev->spi);
	spin_unlock_irq(&plcdev->spi_lock);

	if (spi == NULL)
		return -ESHUTDOWN;

	/* use the buffer lock here for triple duty:
	 *  - prevent I/O (from us) so calling spi_setup() is safe;
	 *  - prevent concurrent SPI_IOC_WR_* from morphing
	 *    data fields while SPI_IOC_RD_* reads them;
	 *  - SPI_IOC_MESSAGE needs the buffer locked "normally".
	 */

	mutex_lock(&plcdev->buf_lock);
	switch (cmd) {
	/* read requests */
	case SPI_IOC_RD_MODE:
		retval = __put_user(spi->mode & SPI_MODE_MASK,
					(__u8 __user *)arg);
		break;
	case SPI_IOC_RD_LSB_FIRST:
		retval = __put_user((spi->mode & SPI_LSB_FIRST) ?  1 : 0,
					(__u8 __user *)arg);
		break;
	case SPI_IOC_RD_BITS_PER_WORD:
		retval = __put_user(spi->bits_per_word, (__u8 __user *)arg);
		SPI_BITS = spi->bits_per_word;
		break;
	case SPI_IOC_RD_MAX_SPEED_HZ:
		retval = __put_user(spi->max_speed_hz, (__u32 __user *)arg);
		SPI_SPEED_USE = spi->max_speed_hz;
		break;

	/* write requests */
	case SPI_IOC_WR_MODE:
		retval = __get_user(tmp, (u8 __user *)arg);
		if (retval == 0) {
			u8	save = spi->mode;

			if (tmp & ~SPI_MODE_MASK) {
				retval = -EINVAL;
				break;
			}

			tmp |= spi->mode & ~SPI_MODE_MASK;
			spi->mode = (u8)tmp;
			retval = spi_setup(spi);
			if (retval < 0)
				spi->mode = save;
			else
				dev_dbg(&spi->dev, "spi mode %02x\n", tmp);
		}
		break;
	case SPI_IOC_WR_LSB_FIRST:
		retval = __get_user(tmp, (__u8 __user *)arg);
		if (retval == 0) {
			u8	save = spi->mode;

			if (tmp)
				spi->mode |= SPI_LSB_FIRST;
			else
				spi->mode &= ~SPI_LSB_FIRST;
			retval = spi_setup(spi);
			if (retval < 0)
				spi->mode = save;
			else
				dev_dbg(&spi->dev, "%csb first\n",
						tmp ? 'l' : 'm');
		}
		break;
	case SPI_IOC_WR_BITS_PER_WORD:
		retval = __get_user(tmp, (__u8 __user *)arg);
		if (retval == 0) {
			u8	save = spi->bits_per_word;

			spi->bits_per_word = tmp;
			SPI_BITS = spi->bits_per_word;
			retval = spi_setup(spi);
			if (retval < 0)
				spi->bits_per_word = save;
			else
				dev_dbg(&spi->dev, "%d bits per word\n", tmp);
		}
		break;
	case SPI_IOC_WR_MAX_SPEED_HZ:
		retval = __get_user(tmp, (__u32 __user *)arg);
		if (retval == 0) {
			u32	save = spi->max_speed_hz;

			spi->max_speed_hz = tmp;
			SPI_SPEED_USE = spi->max_speed_hz;
			retval = spi_setup(spi);
			if (retval < 0)
				spi->max_speed_hz = save;
			else
				dev_dbg(&spi->dev, "%d Hz (max)\n", tmp);
		}
		break;
	case PLC_RESET_MODE:
		printk(KERN_INFO "reset plc\n");
		reset_plc();
		break;
	case PLC_TXRATE_GET:
		if(plcdev->tx_attemp>0 && (plcdev->tx_attemp>=plcdev->tx_count)){
		if(((100*plcdev->tx_count)%plcdev->tx_attemp)>(plcdev->tx_attemp/2))
			tx_rate = (100*plcdev->tx_count)/plcdev->tx_attemp+1;
		else
			tx_rate = (100*plcdev->tx_count)/plcdev->tx_attemp;
		retval = __put_user((u8)tx_rate,(__u8 __user *)arg);
		}
		else
			retval = -EINVAL;
	    break;
	default:
		if(!is_plc_cnfed()){
		/* segmented and/or full-duplex I/O request */
		if (_IOC_NR(cmd) != _IOC_NR(SPI_IOC_MESSAGE(0))
				|| _IOC_DIR(cmd) != _IOC_WRITE) {
			retval = -ENOTTY;
			break;
		}

		tmp = _IOC_SIZE(cmd);
		if ((tmp % sizeof(struct spi_ioc_transfer)) != 0) {
			retval = -EINVAL;
			break;
		}
		n_ioc = tmp / sizeof(struct spi_ioc_transfer);
		if (n_ioc == 0)
			break;
		if (n_ioc > 1){
			retval = -EINVAL;
			break;
		}
		/* copy into scratch area */
		ioc = kmalloc(tmp, GFP_KERNEL);
		if (!ioc) {
			retval = -ENOMEM;
			break;
		}
		if (__copy_from_user(ioc, (void __user *)arg, tmp)) {
			kfree(ioc);
			retval = -EFAULT;
			break;
		}
        if(ioc->len != 38){
        	retval = -EINVAL;
            break;
        }
		/* translate to spi_message, execute */
		retval = spidev_message(plcdev, ioc, n_ioc);
		kfree(ioc);
#if 0
		j1 = jiffies + 100;
		while(time_before(jiffies, j1)){
		if(is_plc_cnfed()){
			enable_irq(gpio_to_irq(PLC_INT));
			break;
		}
		}
		retval = -EINVAL;
#endif
		udelay(100);
		if(is_plc_cnfed()){
		  enable_irq(gpio_to_irq(PLC_INT));
		  break;
		}
		retval = -EINVAL;
		break;
		}
		else{
			retval = -ENOTTY;
			break;
		}
	}
	mutex_unlock(&plcdev->buf_lock);

	spi_dev_put(spi);
	return retval;
}


static irqreturn_t plc_interrupt_handler(int irq, void *dev_id)
{
	struct plcdev_data *plcdev;
    static long int int_count = 0;

	plcdev = dev_id;
	int_count++;

	if(plcdev->plc_status == RX){
	if(spi_asyncput(plcdev, (u8 *)(&varNOP) ))
		    return IRQ_HANDLED;

	return IRQ_WAKE_THREAD;
	}

	if(plcdev->plc_status == TX){
	if (!work_pending(&plcdev->plc_tx_packet)){
		queue_work(plcdev->plc_tx_wq, &plcdev->plc_tx_packet);
	 }
	}

	return IRQ_HANDLED;
}


/* Driver methods */
struct file_operations plc_ops = {
.owner = THIS_MODULE,
.open = plc_open,
.release = plc_close,
.write = plc_write,
.read = plc_read,
.poll = plc_poll,
.unlocked_ioctl = plc_ioctl,
};

/***********add more kobjects here;it is better than proc*******/
static struct bin_attribute plcio_attr = {
	.attr = {
		.name = "plcio",
		.mode = S_IRUGO | S_IWUSR,
	},
	.size = 0,
	.read = plc_kobject_read,
};

static ssize_t plc_kobject_read(struct file *filp, struct kobject *k_obj,
		  struct bin_attribute *attr,
		  char *buf, loff_t off, size_t size)
{
	u8 temp[BUF_SIZE*3];
    int count, status=0,i;
    struct plcdev_data  *plcdev;
    struct device     *Dev;
    struct spi_device *spi;

    Dev = container_of(k_obj, struct device, kobj);
    spi = container_of(Dev, struct spi_device, dev);
    plcdev = spi_get_drvdata(spi);

    mutex_lock(&plcdev->buf_lock);
    if(plcdev->count > 0 && plcdev->count < BUF_SIZE && (plcdev->bufattr != o)){
    	memcpy(buf, plcdev->buffer, plcdev->count);
    	count = plcdev->count;
    	if(plcdev->bufattr==w)
          temp[0] = 'w';
    	if(plcdev->bufattr==r)
    	  temp[0] = 'r';
    	plcdev->bufattr = o;
    }
    else count = 0;
    mutex_unlock(&plcdev->buf_lock);

    if(count){
    for(i=0;i<count;i++){
    	sprintf(&temp[i*3+1],"%02x", buf[i]);
    	temp[(i+1)*3] = ' ';
    }
    temp[3*count] ='\r';
    temp[3*count+1] ='\n';
    status = 3*count+2;
    memcpy(buf, temp, status);
    }
    else status = count;

    return status;
}

static DEVICE_ATTR(plc_txrate, (S_IRUGO | S_IWUSR), plc_kobject_show, NULL);
static DEVICE_ATTR(plc_rxoverrun, (S_IRUGO | S_IWUSR), plc_rxoverrun_show, NULL);
static struct attribute *plcattrs[] = {
		&dev_attr_plc_txrate.attr,
		&dev_attr_plc_rxoverrun.attr,
		NULL,
};
static struct attribute_group plcattr_group = {
		.name = NULL,	/* put in device directory */
		.attrs = plcattrs
};

static ssize_t plc_kobject_show (struct device *d,
		 struct device_attribute *attr, const char *buf, size_t count)
{
	struct plcdev_data  *plcdev;
	struct spi_device *spi;
    int status;
    long int tx_count, tx_attemp;

	    spi = container_of(d, struct spi_device, dev);
	    plcdev = spi_get_drvdata(spi);

	    mutex_lock(&plcdev->buf_lock);
	    tx_count = plcdev->tx_count;
	    tx_attemp = plcdev->tx_attemp;
	    mutex_unlock(&plcdev->buf_lock);
#ifdef PLC_DEBUG
	    printk(KERN_INFO "plc_tx_attemp:%d\n", atomic_read(&plcdev->tx_attemp));
	    printk(KERN_INFO "plc_tx_count:%d\n",  atomic_read(&plcdev->tx_count));
#endif
	    if(!tx_attemp || (tx_attemp < tx_count))
	    	status = 0;
	    else{
	     sprintf( (char *)(&buf[0]),"%3d%s",(int)((100*tx_count)/tx_attemp),"\r\n");
	     status = 5;
	    }
	    return status;
}

static ssize_t plc_rxoverrun_show (struct device *d,
		 struct device_attribute *attr, const char *buf, size_t count)
{
	struct plcdev_data  *plcdev;
	struct spi_device *spi;
    int len;

	    spi = container_of(d, struct spi_device, dev);
	    plcdev = spi_get_drvdata(spi);

	    len = sprintf( (char *)(&buf[0]),"%d%s",plcdev->rxor,"\r\n");

	    return len;
}
/*****************************************************/
static int  plc_spi_probe(struct spi_device *spi)
{
	int status, i;
	u8 temp;
    struct device *dev;
    struct plcdev_data *plcdev;
    dev_t devno;

    if (plc_major) {
    	    devno = MKDEV(plc_major, plc_minor);
    	    status = register_chrdev_region(devno, plc_nr_devs, "plc");
    	 } else {
    	    status = alloc_chrdev_region(&devno, plc_minor, plc_nr_devs,"plc");

    	    plc_major = MAJOR(devno);
    	 }
    	 if (status < 0) {
    	    printk(KERN_WARNING "plc: can't get major %d\n", plc_major);
    	    return status;
    	 }
    	 /*
    	 * allocate the devices -- we can't have them static, as the number
    	 * can be specified at load time
    	 */
    	 plcdev = kmalloc(plc_nr_devs * sizeof(struct plcdev_data), GFP_KERNEL);
    	 if (!plcdev) {
         unregister_chrdev_region(devno, plc_nr_devs);
    	 status = -ENOMEM;
    	 //goto fail;  /* Make this more graceful */
    	 return status;
    	 }
    	 memset(plcdev, 0, plc_nr_devs * sizeof(struct plcdev_data));

    	 /* Initialize each device. */
    	for (i = 0; i < plc_nr_devs; i++) {
    	 plcdev->devt = devno;
    	 plcdev->spi =  spi;
    	 plcdev->users = 0;
    	 plcdev->buffer = NULL;
    	 plcdev->bufattr = o;
    	 spin_lock_init(&plcdev->spi_lock);
    	 mutex_init(&plcdev->buf_lock);
    	 //init_waitqueue_head(&plcdev->plc_wait_queue);
    	 plc_setup_cdev(plcdev, i);
    	 // initializing workqueue
    	 //plcdev->plc_rx_wq = create_singlethread_workqueue("plc_rx_wq");
     	}
    dev = device_create(plcdev_class, &spi->dev, plcdev->devt,
    				    plcdev, "plc%d.%d",
    				    spi->master->bus_num, spi->chip_select);
    status = IS_ERR(dev) ? PTR_ERR(dev) : 0;

    if(status){
    	printk(KERN_ALERT "can not create plc device\n");
        
        device_destroy(plcdev_class, plcdev->devt);
        unregister_chrdev_region(devno, plc_nr_devs);

    	kfree(plcdev);
    	return status;
    }

	// initalizing SPI interface
	plcdev->spi->max_speed_hz = SPI_SPEED_USE; // get this from your SPI device's datasheet
	temp = SPI_MODE_USE;
	temp |= spi->mode & ~SPI_MODE_MASK;
	spi->mode = (u8)temp;
	plcdev->spi->bits_per_word = BIT_PER_WORD;

	status = spi_setup(plcdev->spi);
	if(status){
		printk(KERN_ALERT "can not setup spi device\n");

                device_destroy(plcdev_class, plcdev->devt);
                unregister_chrdev_region(devno, plc_nr_devs);
                
		kfree(plcdev);
		return status;
	}

	status = sysfs_create_bin_file(&spi->dev.kobj, &plcio_attr);
	if (status){
		printk(KERN_ALERT "can not create sysfs bin\n");
		kfree(plcdev);
		return status;
	}

	// create the files associated with this kobject
   status = sysfs_create_group(&spi->dev.kobj, &plcattr_group);
	if (status){
		//kobject_put(&spi->dev.kobj);
		printk(KERN_ERR "unable to create sysfs att\n");

                device_destroy(plcdev_class, plcdev->devt);
                unregister_chrdev_region(devno, plc_nr_devs);
		kfree(plcdev);
		return status;
		}
	spi_set_drvdata(spi, plcdev);
	printk(KERN_INFO "spi device probed @0x%x\n",(int)(plcdev->spi));

	return status;
}

static void plcdev_free(struct plcdev_data *plc_dev)
{
  if(plc_dev)
  {
    //mutex_lock(&plc_dev->buf_lock);
    if(plc_dev->rxbuf)
    {
        kfree(plc_dev->rxbuf);
        plc_dev->rxbuf = NULL;
    }
    if(plc_dev->buffer)
    {
        kfree(plc_dev->buffer);
        plc_dev->buffer = NULL;
    }

    //mutex_unlock(&plc_dev->buf_lock);

    kfree(plc_dev);
  }
}

static int plc_spi_remove(struct spi_device *spi)
{
	struct plcdev_data	*plc_dev = spi_get_drvdata(spi);
    int i;

     sysfs_remove_group(&spi->dev.kobj, &plcattr_group);
     //destroying the sysfs structure
     sysfs_remove_bin_file(&spi->dev.kobj, &plcio_attr);

	 /* Get rid of our char dev entries */
		if (plc_dev) {
		 for (i = 0; i < plc_nr_devs; i++) {
		     cdev_del(&plc_dev->cdev);
		     //flush_workqueue(plc_dev->plc_rx_wq);
   	         //destroy_workqueue(plc_dev->plc_rx_wq);
		 }

        unregister_chrdev_region(plc_dev->devt, plc_nr_devs);

	/* make sure ops on existing fds can abort cleanly */
		spin_lock_irq(&plc_dev->spi_lock);
		plc_dev->spi = NULL;
		spi_set_drvdata(spi, NULL);
		spin_unlock_irq(&plc_dev->spi_lock);

		device_destroy(plcdev_class, plc_dev->devt);
		if (plc_dev->users == 0)
				plcdev_free(plc_dev);//kfree(plc_dev);
                              
		}

	return 0;
}

static const struct of_device_id plc_spi_of_match[] = {
		   {.compatible = "linux,plc"},
    	   { },
};
MODULE_DEVICE_TABLE(of, plc_spi_of_match);

static struct spi_driver plc_spi_driver = {
	.driver = {
		.name	= "plc",
		.owner	= THIS_MODULE,
		.of_match_table = of_match_ptr(plc_spi_of_match),
	},
	.probe	= plc_spi_probe,
	.remove	= plc_spi_remove,

};


/*
* Set up the char_dev structure for this device.
*/
static void plc_setup_cdev(struct plcdev_data *dev, int index)
{
    int err, devno = MKDEV(plc_major, plc_minor + index);

        cdev_init(&dev->cdev, &plc_ops);
        dev->cdev.owner = THIS_MODULE;
        dev->cdev.ops = &plc_ops;
        err = cdev_add (&dev->cdev, devno, 1);
        /* Fail gracefully if need be */
        if (err)
           printk(KERN_ALERT "Error %d adding plc%d", err, index);
}

/* Module Exit */
static void  __exit exit_plc(void)
{
	//int i;
	//dev_t devno = MKDEV(plc_major, plc_minor);

	 if(test_bit(0, &gpio_pin_flags))
		 gpio_free(DEBUG_LED);
	 if(test_bit(1, &gpio_pin_flags))
		 gpio_free(PLC_RST);
	 if(test_bit(2, &gpio_pin_flags))
		 gpio_free(PLC_INT);
	 if(test_bit(3, &gpio_pin_flags))
	 		 gpio_free(PLC_CNF);

    spi_unregister_driver(&plc_spi_driver);

    /* cleanup_module is never called if registering failed */
    class_destroy(plcdev_class);

    printk(KERN_DEBUG "(:(:(:Kernel plc module Removed!:):):)\n");
}

/* Module Initialization */
static int __init  plc_init(void)
{
	int result;

	plcdev_class = class_create(THIS_MODULE, "plcdev");

    if (!gpio_is_valid(DEBUG_LED)){
     printk(KERN_ALERT "PLC Debug LED not available\n");
     result = -EINVAL;
     goto fail;  /* Make this more graceful */
    }
  /*we have requested valid gpios*/
  if((result=gpio_request(DEBUG_LED, "caicai-gpio"))){
    printk(KERN_ALERT "Unable to request caicai-gpio %d\n", DEBUG_LED);
    result = -EINVAL;
    goto fail;  /* Make this more graceful */
   }
   set_bit(0, &gpio_pin_flags);

  /*set gpio direction*/
  if( (result=gpio_direction_output(DEBUG_LED, 1)) < 0 ){
    printk(KERN_ALERT "can not set caicai-gpio output\n");
    result = -EINVAL;
    goto fail;  /* Make this more graceful */
  }
  DEBUG_LED_ON;

  if (!gpio_is_valid(PLC_RST)){
      printk(KERN_ALERT "PLC_RST pin not available\n");
      result = -EINVAL;
      goto fail;  /* Make this more graceful */
    }
    /*we have requested  valid gpios*/
    if((result=gpio_request(PLC_RST, "plc_rst"))){
      printk(KERN_ALERT "Unable to request plc_rst %d\n", PLC_RST);
      result = -EINVAL;
      goto fail;  /* Make this more graceful */
     }
    set_bit(1, &gpio_pin_flags);

    /*set gpio direction*/
    if( (result=gpio_direction_output(PLC_RST, 1)) < 0 ){
      printk(KERN_ALERT "can not set plc_rst output\n");
      goto fail;  /* Make this more graceful */
    }
    PLC_RST_HI;

#if 1
    if (!gpio_is_valid(PLC_INT)){
          printk(KERN_ALERT "PLC_INT pin not available\n");
          result = -EINVAL;
          goto fail;  /* Make this more graceful */
        }
        /*we have requested  valid gpios*/
        if((result=gpio_request(PLC_INT, "plc_int"))){
          printk(KERN_ALERT "Unable to request plc_int %d\n", PLC_INT);
          goto fail;  /* Make this more graceful */
         }
        set_bit(2, &gpio_pin_flags);

        /*set gpio direction*/
         if( (result=gpio_direction_input(PLC_INT)) < 0 ){
           printk(KERN_ALERT "can not set int gpio input\n");
           goto fail;  /* Make this more graceful */
         }
#endif

         if (!gpio_is_valid(PLC_CNF)){
                   printk(KERN_ALERT "PLC_CNF pin not available\n");
                   result = -EINVAL;
                   goto fail;  /* Make this more graceful */
                 }
                 /*we have requested  valid gpios*/
                 if((result=gpio_request(PLC_CNF, "plc_cnf"))){
                   printk(KERN_ALERT "Unable to request plc_cnf %d\n", PLC_CNF);
                   goto fail;  /* Make this more graceful */
                  }
                 set_bit(3, &gpio_pin_flags);

           /*set gpio direction*/
            if( (result=gpio_direction_input(PLC_CNF)) < 0 ){
            printk(KERN_ALERT "can not set cnf gpio input\n");
                   goto fail;  /* Make this more graceful */
             }


    if (!gpio_is_valid(GPIO_RX_SWITCH))
    {
        printk(KERN_ALERT "GPIO_RX_SWITCH not available\n");
        result = -EINVAL;
        goto fail;  /* Make this more graceful */
    }
    //dbgPlcInit((KERN_ERR "GPIO_RX_SWITCH available, \n"));

    /*we have requested valid gpios*/
    if((result=gpio_request(GPIO_RX_SWITCH, "caicai-gpio")))
    {
       printk(KERN_ALERT "Unable to request caicai-gpio %d\n", GPIO_RX_SWITCH);
       result = -EINVAL;
       goto fail;  /* Make this more graceful */
    }
    //dbgPlcInit((KERN_ERR "GPIO_RX_SWITCH request OK, \n"));
    set_bit(4, &gpio_pin_flags);

    /*set gpio direction and initial value:0(low)*/
    if( (result=gpio_direction_output(GPIO_RX_SWITCH, 0)) < 0 )
    {
      printk(KERN_ALERT "can not set caicai-gpio output\n");
      result = -EINVAL;
      goto fail;  /* Make this more graceful */
    }
    //dbgPlcInit((KERN_ERR "GPIO_RX_SWITCH set direction output, \n"));




        result=spi_register_driver(&plc_spi_driver);//trigger probe

        if(result<0){
        printk(KERN_ALERT "spi_register failed\n");
        goto fail;  /* Make this more graceful */
        }
        printk(KERN_DEBUG "(:(:(:Kernel plc module(no opt) Ready!:):):)\n");
        return 0;/* ah ah ...*/

        fail:
         exit_plc();
         return result;
}

/* Module Exit */
static void  __exit plc_exit(void)
{
	//int i;
	//dev_t devno = MKDEV(plc_major, plc_minor);

	 if(test_bit(0, &gpio_pin_flags))
		 gpio_free(DEBUG_LED);
	 if(test_bit(1, &gpio_pin_flags))
		 gpio_free(PLC_RST);
	 if(test_bit(2, &gpio_pin_flags))
		 gpio_free(PLC_INT);
	 if(test_bit(3, &gpio_pin_flags))
	 		 gpio_free(PLC_CNF);

	 if(test_bit(4, &gpio_pin_flags))
	 		 gpio_free(GPIO_RX_SWITCH);

    spi_unregister_driver(&plc_spi_driver);

    /* cleanup_module is never called if registering failed */
    class_destroy(plcdev_class);

    printk(KERN_DEBUG "(:(:(:Kernel plc module(no opt) Removed!:):):)\n");
}

module_init(plc_init);
module_exit(plc_exit);



