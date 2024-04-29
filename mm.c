/* 매크로, 상수 선언*/
#define WSIZE   4           // 32bit 환경에서 한번에 처리할 수 있응 bit수 = 32bit = 4byte
                            // 의미하는바: 정보저장의 최소단위
#define DSiZE   8           // 2 WSIZE * 2 = 두개의 word이동을 위한 임의의 값
#define CHUNKSIZE (1<<12)   // 함번에 로드하는 block사이즈 == os 에서 지정한 page size -> 한번 가용 메모리(haep)확장시, 4kb만큼(한페이지) 확장

#define MAX(x, y)   ((x) > (y)? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))        // bit연산(or) -> 1gyte= 32bit = 0b1000 마지막 3개 비트는 사용 안함
                                                    // 마지막 세개bit를 allocated bit로 사용하고 size계산할때는 모두 0이라고 가정하면 됨 (A)
#define GET(p) (*(unsigned int *)(p))               // p애 저장된 부호없는 int의값(논리적 주소)을 반환
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // 해당 포인터(p)에 부호없는 int의값(논리적 주소)을 저장

#define GET_SIZE(p) (GET(p) & ~0x7)                 // 논리연산 주석(A)에서 설명한 0이라고 가정하고 size를 계산하디 위함
                                                    // ~0x7 = 0b11(생략)11000 과 bit& 연산하면 마지막 3개의 bit가 0인 p가 반환
#define GET_ALLOC(p) (GET(p) & 0x1)                 // 0x1 = 0b00(생략)0001 과 bit& 연산하면 마지막 1개의 bit가 반환

#define HDRP(bp) ((char *)(bp) - WSIZE)             // 현재 블록의 HEADER위치 반환 : bp가 payload(data block)의 시작점에 있다면, 한블록 앞은 header 것 이다.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSiZE)    // 현재 블록의 footer위치 반환 : bp가 payload(data block)의 시작점에 있다면,
                                                                //  현재 블록 사이즈 뒤의 위치는 다음 블록payload(data block)의 시작점이고 두 블록 앞은 footer일 것 이다.

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSiZE)))

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 명시적 가용 구현때, prev / next 기입하기 위해 단위 변경

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)   //ALIGN block size = heaeder+footer(= ALIGNMENT) + data_block_size
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))             

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static char *heap_listp = 0;
static char *rover;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1) return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSiZE, 1));    //prologue_header = doubleword/1
    PUT(heap_listp + (2*WSIZE), PACK(DSiZE, 1));    //prologue_footer = doubleword/1
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        //epliogue = 0/1
    heap_listp += (2*WSIZE);                        //prologue의 가상 payload 주소

    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;   // CHUNKSIZE / WSIZE = chunk:페이지 크기
                                                            // 몇개의 word를 확장할지 결정
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;                                                   // 1byte단위 자료형
    size_t size;                                                // 부호없는 int 자료형
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;     // -> 짝수단위로 올림처리해서 확장

    if((long)(bp = mem_sbrk(size)) == -1) return NULL;          // haep을 실질적으로 확장후 기존의 bp반남

    PUT(HDRP(bp), PACK(size, 0));                               // 확장한 전체 block 은 한덩어리의 block으로 처리
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    if(!GET_ALLOC(HDRP(PREV_BLKP(bp)))){  // 이전 블록이 할당되어 있지 않으면 병합
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;                                        // 병합
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0) return NULL;
    if(size <= DSiZE) asize = 2*DSiZE;
    else asize = DSiZE * ((size + (DSiZE) + (DSiZE - 1)) / DSiZE);
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t oldSize, newSize, copySize;
    
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    oldSize = GET_SIZE(HDRP(oldptr)) - DSiZE;
    newSize = size;
    copySize = oldSize < newSize ? oldSize : newSize;
    memcpy(newptr, oldptr, copySize);

    mm_free(ptr);
    return newptr;
}

static void *find_fit(size_t asize){
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) > (2*DSiZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
