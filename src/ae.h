/* A simple event-driven programming library. Originally I wrote this code
 * for the Jim's event-loop (Jim is a Tcl interpreter) but later translated
 * it in form of a library for easy reuse.
 *
 * Copyright (c) 2006-2012, Salvatore Sanfilippo <antirez at gmail dot com>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *   * Redistributions of source code must retain the above copyright notice,
 *     this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of Redis nor the names of its contributors may be used
 *     to endorse or promote products derived from this software without
 *     specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef __AE_H__
#define __AE_H__

#include "monotonic.h"

#define AE_OK 0
#define AE_ERR -1

#define AE_NONE 0       /* 未注册任何事件。*/
#define AE_READABLE 1   /* 当描述符可读时触发。*/
#define AE_WRITABLE 2   /* 当描述符可写时触发。*/
#define AE_BARRIER 4    /* 使用可写，如果可读事件已在同一事件循环迭代中触发则不触发。当您希望在发送答复之前将内容保存到磁盘并希望以group方式执行此操作时，非常有用。*/

#define AE_FILE_EVENTS (1<<0)
#define AE_TIME_EVENTS (1<<1)
#define AE_ALL_EVENTS (AE_FILE_EVENTS|AE_TIME_EVENTS)
#define AE_DONT_WAIT (1<<2)
#define AE_CALL_BEFORE_SLEEP (1<<3)
#define AE_CALL_AFTER_SLEEP (1<<4)

#define AE_NOMORE -1
#define AE_DELETED_EVENT_ID -1

/* Macros */
#define AE_NOTUSED(V) ((void) V)

struct aeEventLoop;

/*类型和数据结构*/
typedef void aeFileProc(struct aeEventLoop *eventLoop, int fd, void *clientData, int mask);
typedef int aeTimeProc(struct aeEventLoop *eventLoop, long long id, void *clientData);
typedef void aeEventFinalizerProc(struct aeEventLoop *eventLoop, void *clientData);
typedef void aeBeforeSleepProc(struct aeEventLoop *eventLoop);

/*文件事件结构*/
typedef struct aeFileEvent {
    int mask;               /* 存储监控的文件事件类型 AE_(READABLE|WRITABLE|BARRIER)中的一种  */
    aeFileProc *rfileProc;  /* 函数指针，指向读事件处理函数 */
    aeFileProc *wfileProc;  /* 函数指针，指向写事件处理函数 */
    void *clientData;       /* 指向对应的客户端对象 */
} aeFileEvent;

/*时间事件结构*/
typedef struct aeTimeEvent {
    long long id;                          /* 时间事件标识符。通过字段eventLoop->timeEventNextId实现 */
    monotime when;                         /* 事件触发的时间 */
    aeTimeProc *timeProc;                  /* 函数指针，指向时间事件处理函数 */
    aeEventFinalizerProc *finalizerProc;   /* 函数指针，删除时间事件节点之前会调用此函数 */
    void *clientData;                      /* 指向对应的客户端对象 */
    struct aeTimeEvent *prev;              /* 指向上一个时间事件节点 */
    struct aeTimeEvent *next;              /* 指向下一个时间事件节点 */
    int refcount;                          /* 引用计数，以防止计时器事件出现在递归时间事件调用中释放。*/
} aeTimeEvent;

/*已触发的事件*/
typedef struct aeFiredEvent {
    int fd;             /*已触发的文件描述符*/
    int mask;           /*事件类型掩码*/
} aeFiredEvent;

/*基于事件的程序的状态*/
typedef struct aeEventLoop {
    int maxfd;                      /* 当前注册的最高文件描述符*/
    int setsize;                    /* 跟踪的最大文件描述符数*/
    long long timeEventNextId;      /* 下一个时间事件的ID */
    aeFileEvent *events;            /* 已注册的事件数组*/
    aeFiredEvent *fired;            /* 已触发的事件数组*/
    aeTimeEvent *timeEventHead;     /* 时间事件链表的头 */
    int stop;                       /* 是否停止（0：否；1：是）*/
    void *apidata;                  /* 各平台polling API所需的特定数据 */
    aeBeforeSleepProc *beforesleep; /* 事件循环休眠开始的处理函数 */
    aeBeforeSleepProc *aftersleep;  /* 事件循环休眠结束的处理函数 */
    int flags;
} aeEventLoop;

/* Prototypes */
aeEventLoop *aeCreateEventLoop(int setsize);
void aeDeleteEventLoop(aeEventLoop *eventLoop);
void aeStop(aeEventLoop *eventLoop);
int aeCreateFileEvent(aeEventLoop *eventLoop, int fd, int mask,
        aeFileProc *proc, void *clientData);
void aeDeleteFileEvent(aeEventLoop *eventLoop, int fd, int mask);
int aeGetFileEvents(aeEventLoop *eventLoop, int fd);
long long aeCreateTimeEvent(aeEventLoop *eventLoop, long long milliseconds,
        aeTimeProc *proc, void *clientData,
        aeEventFinalizerProc *finalizerProc);
int aeDeleteTimeEvent(aeEventLoop *eventLoop, long long id);
int aeProcessEvents(aeEventLoop *eventLoop, int flags);
int aeWait(int fd, int mask, long long milliseconds);
void aeMain(aeEventLoop *eventLoop);
char *aeGetApiName(void);
void aeSetBeforeSleepProc(aeEventLoop *eventLoop, aeBeforeSleepProc *beforesleep);
void aeSetAfterSleepProc(aeEventLoop *eventLoop, aeBeforeSleepProc *aftersleep);
int aeGetSetSize(aeEventLoop *eventLoop);
int aeResizeSetSize(aeEventLoop *eventLoop, int setsize);
void aeSetDontWait(aeEventLoop *eventLoop, int noWait);

#endif
