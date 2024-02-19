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


/*
! 주소관리법 실패 이유 :
! 1. free_list 와 free_end 값으로 가용 리스트의 시작과 끝을 연결하여 circuler 로 구현
! 2. 새롭게 free 된 블록에 대해서 인접 가용 리스트를 조회하여 삽입해주는 함수가 X
! 3. circuler를 통해 free 블록에 접근 실패하여 결국 extend heap을 계속 생성
 */

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
#define PUT(p, val)         (*(unsigned int *)(p) = (size_t)(val))

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

/* explict free list 주소 기준법 정의 */
typedef struct {
  char *start;
  char *end;
} explict_t;

static explict_t free_list;

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
  {
    if (free_list.end != free_list.start) 
    {
      if (bp < free_list.start) 
      {
          // 다음 노드의 prev를 나로 변경
          PUT(PREV_FBLKP(free_list.start), bp);
          // 지금 노드의 next에 다음노드 주소 저장
          PUT(NEXT_FBLKP(bp),free_list.start);
          //start를 나로
          free_list.start=bp;
          // 시작 노드의 prev는  end로 써클연결 monster
          PUT(PREV_FBLKP(bp),free_list.end);
      } 
      else if (bp > free_list.end) 
      {
        // 이전 노드의 next를 나로 변경
        PUT(NEXT_FBLKP(free_list.end), bp);
        // 지금 노드의 prev에 이전노드 주소 저장
        PUT(PREV_FBLKP(bp),free_list.end);
        //end를 나로
        free_list.end=bp;
        // 마지막 노드의 next는 시작점으로 써클연결 monster
        PUT(NEXT_FBLKP(bp),free_list.start);
      }
      else  
      {
        // printf("!!!\n");
        PUT(NEXT_FBLKP(PREV_FBLKP(bp)) , bp);
        PUT(PREV_FBLKP(NEXT_FBLKP(bp)) , bp);
        // 여기 
        PUT(NEXT_FBLKP(bp), NEXT_BLKP(bp));
        PUT(PREV_FBLKP(bp), PREV_BLKP(bp)); 
      }
    }
    
    return bp;
  }

  /* case 2 : 이전 블록은 할당 O , 다음 블록이 할당 X */
  else if (prev_alloc && !next_alloc)
  {
    // printf("!!\n");
    char *next = NEXT_BLKP(bp);

    if (bp < free_list.start) 
    {
      // 여기
      PUT(NEXT_FBLKP(bp), NEXT_FBLKP(next));
      PUT(PREV_FBLKP(bp), PREV_FBLKP(next));
      free_list.start = bp;
      PUT(NEXT_FBLKP(free_list.end), bp);
    }

    else 
    {
      //여기
      PUT(NEXT_FBLKP(bp), NEXT_FBLKP(next));
      PUT(PREV_FBLKP(bp), PREV_FBLKP(next));
    }

    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  /* case 3: */
  else if (!prev_alloc && next_alloc) 
  {
    // printf("!!\n");
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  /* case 4: */
  else
  {
    if (NEXT_BLKP(bp) == free_list.end)
      free_list.end = PREV_BLKP(bp);

    PUT(NEXT_FBLKP(PREV_BLKP(bp)), NEXT_FBLKP(NEXT_BLKP(bp)));
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

  /* Initialize free block header/footer and the epilogue header*/
  PUT(HDRP(bp), PACK(size, 0));         /* Free block header*/
  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer*/

  PUT(NEXT_FBLKP(bp), 1);              /*다음 프리블럭 포인터*/
  PUT(PREV_FBLKP(bp), 1);              /* 이전 프리블럭 포인터*/
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header*/

  /* case 1 : 처음이면 */
  if (free_list.start == NULL && free_list.end == NULL) {
      free_list.start = free_list.end=bp;
      PUT(NEXT_FBLKP(bp), bp);
      PUT(PREV_FBLKP(bp), bp);
  }
  /* case 2 : 다음에 가용할 리스트가 있다면? */

  return coalesce(bp);  //코올레스
}

/*
 * ***** * ***** * ***** * ***** * 블록 할당 공간 검색 * ***** * ***** * ***** * ***** 
 */
static void *find_fit(size_t adj_size)
{
  /* first fit */
  // void *bp;
  // for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
  // {
  //   if(!GET_ALLOC(HDRP(bp)) && (adj_size <= GET_SIZE(HDRP(bp))))
  //     return bp;
  // }

  /* New search*/
  char *next=free_list.start;

  do {
    if(adj_size <= GET_SIZE(HDRP(next)))
      return next;

    next = NEXT_FBLKP(next);
  } while (next != free_list.end);

  return NULL;
}

/*
 * ***** * ***** * ***** * ***** * 블록 생성 * ***** * ***** * ***** * ***** 
 */
static void place(void *bp, size_t adj_size)
{
  size_t cur_size = GET_SIZE(HDRP(bp));

  if ((cur_size - adj_size) >= (2*DSIZE))
    {   
      PUT(HDRP(bp), PACK(adj_size, 1));
      PUT(FTRP(bp), PACK(adj_size, 1));
      bp=NEXT_BLKP(bp);
      PUT(HDRP(bp), PACK(cur_size - adj_size, 0));
      PUT(FTRP(bp), PACK(cur_size - adj_size, 0));
      
      // 프리 블록 재생성 -> 프리 블록에게 앞뒤 블록 연결
      // 빈 블록이 하나일 때 
      if (free_list.start == PREV_BLKP(bp) && free_list.end == PREV_BLKP(bp)) 
      {
        free_list.start = bp;
        free_list.end = bp;
      }

      // if 스타트 지점을 옮겨야 할 때
      else if (free_list.start == PREV_BLKP(bp)) 
      {
        free_list.start = bp;
      }

      // if 엔드 지점을 옮겨야 할 때
      else if (free_list.end == PREV_BLKP(bp)) 
      {
        free_list.end = bp;
      }

    PUT(PREV_FBLKP(bp), NEXT_FBLKP(PREV_BLKP(bp)));
    PUT(NEXT_FBLKP(bp), PREV_FBLKP(NEXT_BLKP(bp)));

    PUT(PREV_FBLKP(NEXT_FBLKP(bp)), bp);
    PUT(NEXT_FBLKP(PREV_FBLKP(bp)), bp);
  }
  else
  {
      // 프리 블록 삭제됨 -> 앞뒤 프리 블록 서로 연결
      PUT(HDRP(bp), PACK(cur_size, 1));
      PUT(FTRP(bp), PACK(cur_size, 1));
      if (free_list.start == bp && free_list.end == bp) 
      {
        free_list.end = NULL;
        free_list.start = NULL;
      } 
      else 
      {
        PUT(PREV_FBLKP(bp), NEXT_FBLKP(bp));
        PUT(NEXT_FBLKP(bp), PREV_FBLKP(bp));
      }
  }
}

/* 
 * ***** * ***** * ***** * *** 초기 가용 리스트 생성 *** * ***** * ***** * ***** 
 */
int mm_init(void)
{
  free_list.start = NULL;
  free_list.end = NULL;

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
  
  if (free_list.end == NULL && free_list.start == NULL) 
  {
    free_list.start = bp;
    free_list.end = bp;
  }

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
