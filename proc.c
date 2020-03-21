#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;

int sched_trace_enabled = 1; // for CS350 CPU/process project
int sched_policy = 1;
int RUNNING_THRESHOLD = 2;//2
int WAITING_THRESHOLD = 4;//4

/* ***************************************************************** */
/* Queue Struct */

typedef struct Queue{
  int front, rear, size;
  int max;
  struct proc* arr[NPROC];
} Queue;

void initQueue(Queue* queue){

  queue->front = 0;
  queue->size = 0;
  queue->rear = NPROC-1;
  queue->max = NPROC;
  for(int i = 0; i < NPROC; i++){
    queue->arr[i] = 0;
  }
}
int isFull(Queue* queue){  
  return (queue->size == NPROC);
}

int isEmpty(Queue* queue){
  return (queue->size == 0);
}
//adds proc to queue
int enqueue(Queue* queue, struct proc* p){
  if(p == 0){
    return -1;
  }
  if(isFull(queue)){
    return 0;
  }
  queue->rear = (queue->rear +1)%(queue->max); 
  queue->arr[(queue->rear)] = p;
  queue->size += 1;
  return 1;
  
}
//removes proc from queue
struct proc* dequeue(Queue* queue){
  if(isEmpty(queue)) return 0;
  struct proc* p = queue->arr[queue->front];
  queue->front = ((queue->front)+1)%queue->max;
  queue->size--;
  return p;
}
struct proc* front(Queue* queue){
//returns front of queue NOT DEQUEUE
  if(isEmpty(queue)) return 0;
  return queue->arr[queue->front];
}
struct proc* rear(Queue* queue){
  //returns end of queue NOT DEQUEUE
  if(isEmpty(queue)) return 0;
  return queue->arr[queue->rear];
}

struct proc* remove(Queue* queue, struct proc* removing){
  /*
    unused function, logic is used for promotion (dequeue & enqueue to copy)
  */
  //removes proc in specific queue; returns proc that was removed
  if(removing == 0) cprintf("trying to remove null ptr, something will break\n");
  
  Queue temp;
  initQueue(&temp);
  struct proc * p;
  //copy over to temp
  int found = 0;
  for(int i = 0; i < NPROC; i++){
    p = dequeue(queue);
    if(p == removing){
      found = 1;
      continue;
    }
    enqueue(&temp, p);
    //we skip over the process-to-be-removed in the original queue, and copy others else to temp
  }
  if(found == 0) cprintf("couldn't find proc to remove, something will break\n");
  //temp holds queue-{removing}
  //reset queue, then push all of temp into queue
  initQueue(queue);
  while(!isEmpty(&temp)) enqueue(queue, dequeue(&temp));
  //cprintf("copied everything but pid %d\t\t", removing->pid);
  return removing;
}

int hasRunnable(Queue* queue){
  struct proc* p;
  for(int i = 0; i < NPROC; i++){
    p = queue->arr[i];
    /*if(p!=0 && p->pid ==2){
      cprintf("\npid 2 state: %d \n", p->pid);
    }*/
  
    if((p != 0) && p->state == RUNNABLE) return 1;
  }
  return 0;
}

int queueContainsPID(Queue* queue, int PID){
  acquire(&ptable.lock);
  for(struct proc *p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == PID){
      release(&ptable.lock);
      return 1;
    }
  }
  release(&ptable.lock);
  return 0;
}

Queue queue0; //this needs to be a queue
Queue queue1; //this just needs to be an array

/* ***************************************************************** */


extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;
  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;
  if(p->pid == 1 || p->pid == 2){
    p->priority = 0;
  }
  else{p->priority = 1;}
  p->running_ticks = 0;
  p->waiting_ticks = 0;
  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;
  
  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;
  
  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];
  
  p = allocproc();
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  p->state = RUNNABLE;
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  
  sz = proc->sz;
  if(n > 0){
    if((sz = allocuvm(proc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(proc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  proc->sz = sz;
  switchuvm(proc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;

  // Allocate process.
  if((np = allocproc()) == 0)
    return -1;

  // Copy process state from p.
  if((np->pgdir = copyuvm(proc->pgdir, proc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = proc->sz;
  np->parent = proc;
  *np->tf = *proc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(proc->ofile[i])
      np->ofile[i] = filedup(proc->ofile[i]);
  np->cwd = idup(proc->cwd);

  safestrcpy(np->name, proc->name, sizeof(proc->name));
 
  pid = np->pid;

  // lock to force the compiler to emit the np->state write last.
  acquire(&ptable.lock);
  np->state = RUNNABLE;
  release(&ptable.lock);
  
  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *p;
  int fd;

  if(proc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(proc->ofile[fd]){
      fileclose(proc->ofile[fd]);
      proc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(proc->cwd);
  end_op();
  proc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(proc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == proc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  proc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;

  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for zombie children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != proc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->state = UNUSED;
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || proc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(proc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
/*
incrementWaiting(struct proc * a){
  acquire(&ptable.lock);
  for(struct proc * p = queue0->arr[0]; p < queue0->arr[NPROC]; p++){
    if(a == 0){

    }
  }
}
int hasRunnableProcess(int qNum){

}
void updatePriorities(){

}
*/
void
scheduler(void)
{
  //default sched policy
  if(sched_policy == 0){
    struct proc *p;
    int ran = 0; // CS350: to solve the 100%-CPU-utilization-when-idling problem

    for(;;){
      // Enable interrupts on this processor.
      sti();

      // Loop over process table looking for process to run.
      acquire(&ptable.lock);
      ran = 0;
      for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
        if(p->state != RUNNABLE)
          continue;

        ran = 1;
        
        // Switch to chosen process.  It is the process's job
        // to release ptable.lock and then reacquire it
        // before jumping back to us.
        proc = p;
        switchuvm(p);
        p->state = RUNNING;
        swtch(&cpu->scheduler, proc->context);
        switchkvm();

        // Process is done running for now.
        // It should have changed its p->state before coming back.
        proc = 0;
      }
      release(&ptable.lock);

      if (ran == 0){
          halt();
      }
    }
  }
  else{
  //Implemented sched policy
    //init vars
    struct proc* p;
    struct proc* promo = 0;
    initQueue(&queue0);
    //cprintf("init q0 \n");
    initQueue(&queue1); 
    //cprintf("init q1 \n");
    acquire(&ptable.lock); 
    //everything starts in queue0
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p == 0){
        //cprintf("proc null \n");
        continue;
      }
      p->running_ticks = p->waiting_ticks = 0;
      enqueue(&queue0, p);
    }
    release(&ptable.lock);
    /*

    we can only use priority to check if its 0, non zero means not pinned. Always keep track of 
    waiting ticks and running ticks
    after running, check if eligible for promotion. demotion
    update prios at the start of every loop
    whenever a proc is promod to q0, it must have a running tick of 0
    BUILD:    
        start with 2 round robin queues, and see if promotion and demotion are working properly
        then, change queue1 to be a priority queue
    keep track of waiting ticks and running ticks?
    */
    int ran = 0;
    for(;;){
      sti();
      ran = 0;
      /**** check if any prio 0 procs are in wrong queue****/
      acquire(&ptable.lock);
      struct proc* fix = 0;
      for(int i = 0; i < NPROC; i++){
        fix = dequeue(&queue1);
        if(fix != 0 && fix->pid > 0 && fix->priority == 0){
          //cprintf("fixed error with prio setting in wrong queue, pid %d\n", fix->pid);
          enqueue(&queue0, fix); //wrong queue
        }
        else{
          enqueue(&queue1, fix); //put it back
        }
      }
      //check if any proc is in wrong queue
      
      p = 0;      
      for(int i = 0; i < NPROC; i++){
        //q0
        p = dequeue(&queue0);
        if(p == 0) enqueue(&queue0, p); //put null ptr back
        else if(p->priority == 0) enqueue(&queue0, p); //put pinned procs into q0
        else if(p->running_ticks > RUNNING_THRESHOLD){
          //demote if condition is true
          p->running_ticks = 0;
          p->waiting_ticks = 0;
          enqueue(&queue1, p);
        }
        else enqueue(&queue0, p); //put it back
        p = dequeue(&queue1);
        if(p == 0) enqueue(&queue1, p); //put null ptr back
        else if(p->waiting_ticks > WAITING_THRESHOLD){
          //promote if condition is true
          p->running_ticks = 0;
          p->waiting_ticks = 0;
          enqueue(&queue0, p);
        }
        else enqueue(&queue1, p); //put it back
      }     
      p = 0; 

      
      release(&ptable.lock);
      /*********** ************* ***********/
      /*********** START QUEUE 0 ***********/
      acquire(&ptable.lock);
      for(int i = 0; i<NPROC; i++){
        //skip nullptr
        p = dequeue(&queue0);
        if(p == 0 || p->state != RUNNABLE){
          enqueue(&queue0, p);
          continue;
        }
        //ran a process, don't halt
        ran = 1;
        //increment appropriate ticks
        p->running_ticks++;
        struct proc* q;
        for(int j = 0; j < NPROC; j++){
          q = queue1.arr[j];
          if(q != 0 && q->state == RUNNABLE) q->waiting_ticks++;;
        }        
        //run p
        proc = p;
        switchuvm(p);
        p->state = RUNNING;
        swtch(&cpu->scheduler, proc->context);
        switchkvm();
        proc = 0;
        if(p->priority == 0) enqueue(&queue0, p); //keep procs with prio 0 in queue0
        //demotion via ticks
        else if(p->running_ticks <= RUNNING_THRESHOLD) enqueue(&queue0, p);
        else{
          //proc ran too much, change to queue 1      [demotion] @DEMO
          //cprintf("DEMOTION pid %d, running %d, rthresh %d\n", p->pid, p->running_ticks, RUNNING_THRESHOLD);
          p->running_ticks = 0;
          p->waiting_ticks = 0;

          enqueue(&queue1, p);
        }
        //check if any can be promoted IF RUNNABLE   [promotion]
        promo = 0;
        for(int i = 0; i < NPROC; i++){
          promo = dequeue(&queue1);
          if(promo == 0 || promo->waiting_ticks <= WAITING_THRESHOLD) enqueue(&queue1, promo);
          else{
            //non null proc up for promotion @PROMO
            //cprintf("\nPROMOTION pid %d, waiting %d, wthresh %d\n", promo->pid, promo->waiting_ticks, WAITING_THRESHOLD);
            promo->waiting_ticks = 0;
            promo->running_ticks = 0;
            enqueue(&queue0, promo);
          }
      }
      }
      /*********** END QUEUE 0 ***********/
      release(&ptable.lock);
      
      if(hasRunnable(&queue0)){
        //cprintf("q0 HAS RUNNABLE\n");       
        continue;
      }
      /*********** START QUEUE 1 ***********/
      //if(hasRunnable(&queue1)) cprintf("something to run in q1! RUNNING THRESHOLD %d\n", RUNNING_THRESHOLD);
      acquire(&ptable.lock);
      struct proc* toRun = 0;
      struct proc* current = 0;
      //see if there is a runnable process in queue1; if multiple, find prio val
      for(int i = 0; i<NPROC; i++){
        current = queue1.arr[i];
        //skip nullptr and non runnable proc*'s
        if(current == 0 || current->state != RUNNABLE) continue; 
        if(toRun == 0){
          //first runnable nonnull ptr is the one waiting the longest thus far
          toRun = queue1.arr[i];
        }
        else{ 
          //toRun != 0, current != 0, current->state is runnable 
          if(current->waiting_ticks > toRun->waiting_ticks){
            toRun = current;
          }
        }
      }
      //toRun either has process to run or 0, 0->nothing will run
      if(toRun != 0){
        //cprintf("...running! %d\n", toRun->pid);
        //ran a process, don't halt
        ran = 1;
        //increment appropriate ticks
        struct proc* q;
        for(int j = 0; j < NPROC; j++){
          q = queue1.arr[j];
          if(q != 0 && q != toRun && q->state == RUNNABLE) q->waiting_ticks++;
        }  
        proc = toRun;
        switchuvm(toRun);
        toRun->state = RUNNING;
        swtch(&cpu->scheduler, proc->context);
        switchkvm();
        proc = 0;
      }
      release(&ptable.lock);
      //check if any can be promoted IF RUNNABLE    [promotion]
      promo = 0;
      for(int i = 0; i < NPROC; i++){
        promo = dequeue(&queue1);
        if(promo == 0 || promo->waiting_ticks <= WAITING_THRESHOLD) enqueue(&queue1, promo);
        else{
          //non null proc up for promotion
          //cprintf("\nPROMOTION pid %d, waiting %d, wthresh %d\n", promo->pid, promo->waiting_ticks, WAITING_THRESHOLD);
          promo->waiting_ticks = 0;
          promo->running_ticks = 0;
          enqueue(&queue0, promo);
        }
      }
      /*********** END QUEUE 1 ***********/
      if (ran == 0){       
        halt();
      }
        
    }
  }
    
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state.
void
sched(void)
{
  int intena;
  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(cpu->ncli != 1)
    panic("sched locks");
  if(proc->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = cpu->intena;

  // CS350: print previously running process
  // We skip process 1 (init) and 2 (shell)
  //@HERE
  if ( sched_trace_enabled &&
	proc && proc->pid != 1 && proc->pid != 2)
        cprintf("[%d]", proc->pid);

  swtch(&proc->context, cpu->scheduler);
  cpu->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  proc->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot 
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }
  
  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  if(proc == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }

  // Go to sleep.
  proc->chan = chan;
  proc->state = SLEEPING;
  sched();

  // Tidy up.
  proc->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];
  
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}
int setrunningticks(int running_thres){
  //int old = RUNNING_THRESHOLD;
  RUNNING_THRESHOLD = running_thres;
  //cprintf("\nRUNNING_THRESHOLD changed from %d to %d", old, RUNNING_THRESHOLD);
  return 0;
}
int setwaitingticks(int waiting_thres){
  //int old = WAITING_THRESHOLD;
  WAITING_THRESHOLD = waiting_thres;
  //cprintf("\nWAITING_THRESHOLD changed from %d to %d", old, WAITING_THRESHOLD);
  return 0;
}
int setpriority(int pid, int priority){
  struct proc *p;
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if (p->pid == pid){
      //cprintf("\nPID %d PRIORITY changed from %d to %d", pid, p->priority, priority);
      p->priority = priority;
      return 0;
    }
  }
  return 1;
}
