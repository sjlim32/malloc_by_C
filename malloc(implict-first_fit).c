/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
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
    "6team",
    /* First member's full name */
    "Lim sungjoon",
    /* First member's email address */
    "32sjlim@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* ***** * ***** * ***** * ***** 상수 및 매크로 정의 ***** * ***** * ***** * ***** */

/* single word (4) or double word (8) alignment */
#define WSIZE               4    
#define DSIZE               8         /* header/footer 설정 (bytes) */
#define ALIGNMENT           8         /* bytes */
#define CHUNKSIZE           (1<<12)   /* extend heap 크기 설정 */

/* 메모리 블록을 ALIGN의 배수로 설정 */
#define ALIGN(size)         (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE         (ALIGN(sizeof(size_t)))

#define MAX(x, y)           ((x) > (y)? (x) : (y))

/* 블록의 사이즈와 할당 여부를 저장 */
#define PACK(size, alloc)   ((size) | (alloc))

/* GET = 값을 저장할 주소값(p) / PUT = 주소값에 값(val)을 저장 */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

/* 주소값이 가지고 있는 크기와 할당 여부를 확인 */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

/* 블록 포인터(bp)가 주어질 때, 블록의 헤더와 풋터의 주소값을 확인 */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터(bp)가 주어질 때, 다음 블록과 이전 블록의 주소값을 확인 */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;

/* 
 * ***** * ***** * ***** * *** 가용 리스트 병합 *** * ***** * ***** * ***** 
 */
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));   /* 이전 블록 할당 여부 */
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));   /* 다음 블록 할당 여부 */
  size_t size = GET_SIZE(HDRP(bp));

  /* case 1 : 양 쪽 모두 할당 O */
  if (prev_alloc && next_alloc)
    return bp;

  /* case 2 : 이전 블록은 할당 O , 다음 블록이 할당 X */
  else if (prev_alloc && !next_alloc)
  {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  /* case 3 : 이전 블록이 할당 X, 다음 블록은 할당 O */
  else if (!prev_alloc && next_alloc)
  {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  /* case 4 : 양 쪽 블록이 모두 할당 X*/
  else
  {
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  return bp;
}

/* 
 * ***** * ***** * ***** * *** 가용 리스트 확장 *** * ***** * ***** * ***** 
 */
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  /* */
  size = (words % 2) ? (words + 1) * WSIZE : words *WSIZE;
  if ((bp = mem_sbrk(size)) == (void *)-1)
    return NULL;

  /*  */
  PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));           /* Free blcok footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* NEW epilogue header */

  return coalesce(bp);
}

/*
 * ***** * ***** * ***** * ***** * 블록 할당 공간 검색 * ***** * ***** * ***** * ***** 
 */
static void *find_fit(size_t adj_size)
{
  /* first fit */
  void *bp;
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
  {
    if(!GET_ALLOC(HDRP(bp)) && (adj_size <= GET_SIZE(HDRP(bp))))
      return bp;
  }

  return NULL;
}

/*
 * ***** * ***** * ***** * ***** * 블록 생성 * ***** * ***** * ***** * ***** 
 */
static void place(void *bp, size_t adj_size)
{
  size_t cur_size = GET_SIZE(HDRP(bp));

  /* cur_size(Free block)의 공간에 adj_size를 할당하고도 16bytes 이상 남았을 때, 남은 공간을 다시 Free block으로 할당 */
  if ((cur_size - adj_size) >= (2 * DSIZE))
  {
    PUT(HDRP(bp), PACK(adj_size, 1));
    PUT(FTRP(bp), PACK(adj_size, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(cur_size - adj_size, 0));
    PUT(FTRP(bp), PACK(cur_size - adj_size, 0));
  }
  /* cur_size(Free block)의 공간에 adj_size를 할당하고 16bytes 미만으로 남았을 때, cur_size를 adj_size에게 모두 할당 */
  else
  {
    PUT(HDRP(bp), PACK(cur_size, 1));
    PUT(FTRP(bp), PACK(cur_size, 1));
  }
}

/* 
 * ***** * ***** * ***** * *** 초기 가용 리스트 생성 *** * ***** * ***** * ***** 
 */
int mm_init(void)
{
  /* heap 초기화 및 생성 */
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    return -1;

  PUT(heap_listp, 0);                               /* Alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));    /* Prologue header */
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));        /* Epilogue header */
  heap_listp += (2 * WSIZE);

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;

  return 0;
}

/* 
 * ***** * ***** * ***** * ***** * 메모리에 블록 할당 * ***** * ***** * ***** * ***** 
 */

void *mm_malloc(size_t size)
{
  size_t adj_size;
  size_t ext_size;
  char *bp;

  if (size == 0)
    return NULL;

  /* size가 16 bytes 미만일 때, 16bytes 를 할당 */
  if (size <= DSIZE)
    adj_size = 2 * DSIZE;

  /* size가 16 bytes 이상일 때 */
  else
  {
    // adj_size = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE)   /* 8의 배수로 설정 */
    adj_size = ALIGN(size) + 8;   /* header, footer 추가 */
  }

  /* find_fit 확인 후 free block 이 충분할 때 바로 할당 */
  if ((bp = find_fit(adj_size)) != NULL)
  {
    place(bp, adj_size);
    return bp;
  }

  /* find_fit 확인 후 free block 이 부족할 때, 확장 후 할당 */
  ext_size = MAX(adj_size, CHUNKSIZE);
  if ((bp = extend_heap(ext_size / WSIZE)) == NULL)
    return NULL;
  
  place(bp, adj_size);
  return bp;
}

/* 
 * ***** * ***** * ***** * ***** * 메모리에서 블록 반환 * ***** * ***** * ***** * *****
 */
void mm_free(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}

/*
 * ***** * ***** * ***** * ***** * 메모리에 블록 재할당 * ***** * ***** * ***** * *****
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copy_size;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    // copy_size = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copy_size = *(size_t *)((char *)oldptr - WSIZE) - 9;
    if (size < copy_size)
        copy_size = size;
    memcpy(newptr, oldptr, copy_size);
    mm_free(oldptr);
    return newptr;
}
