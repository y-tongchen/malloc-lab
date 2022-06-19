/* 
 * mm.c
 *
 * This allocater involves a segregated free list and best fit search strategy.
 * As free list is linked in ascending order, best fit search strategy is 
 * implemented by just finding the first fit block
 * 
 * Using the 2nd bit of the 3 free bits to indicate if previous block is free,
 * only free blocks in this allocater have both headers and footers. Allocated
 * blocks only have a header. 
 * 
 * The segregated free lists are doubly linked lists. Every free block 
 * requires two 8-byte spaces to store pointers to previous and next
 * free blocks. Thus, minimum block size is 24 bytes. 
 */ 

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/* Basic constants and macros from mm-textbook.c */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */ 
#define MINBLOCKSIZE 3*DSIZE /* Minimum block size = 24 bytes */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word (4 bytes) at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read and write double word (8 bytes) at address p */
#define GET_8B(p)       (*(size_t *)(p))            
#define PUT_8B(p, val)  (*(size_t *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1) // 1: Allocated ; 0: Free
#define GET_PREV_ALLOC(p) (GET(p) & 0x2) // 1: Prev is allocated; 0: Prev is free

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 
#define PREV_FTRP(bp)  ((char *)(bp) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* For manipulation of segregated free list only.
Get or set prev and next pointer from address p 
64 bit machine = Pointer is 8 bytes = sizeof(size_t) */
#define GET_PREVP(p) (*(size_t *)(p))
#define GET_NEXTP(p) (*((size_t *)(p) + 1))
#define SET_PREVP(p, prev) (*(size_t *)(p) = (prev))
#define SET_NEXTP(p, val) (*((size_t *)(p) + 1) = (val))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to the start of heap */
static char *seg_free_listp = 0;  /* Pointer to the start of segregated free list */


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

/* Function prototypes for manipulating segregated free list */
static void* get_root(size_t size);
static void remove_from_free_list(void *bp);
static void insert_to_free_list(void* bp);


/*
* get_root - Given a size, get the address of the start of the free list
*/
static void* get_root(size_t size) {
    int i = 0;
    if (size <= 32) i=0;
    else if (size <= 64) i=1;
    else if (size <= 128) i=2;
    else if (size <= 256) i=3;
    else if (size <= 512) i=4;
    else if (size <= 1024) i=5;
    else if (size <= 2048) i=6;
    else if (size <= 4096) i=7;
    else if (size <= 8192) i=8;
    else  i=9;
    dbg_printf("get_root: i=%d size=%zu\n", i, size);
    return seg_free_listp + (i*DSIZE);
}

/*
 * remove_from_free_list - remove the block from the segregated free list
                            Link the blocks from left and right
                            Take note: 4 cases on where the block could be removed from
                            Case 1: Prev block is root, next block is NULL
                            Case 2: Prev block is not root, next block is NULL
                            Case 3: Prev block is root, next block is not NUll
                            Case 4: Prev block is not root, next block is not NULL
 */ 
static void remove_from_free_list(void *bp) {
    // Make sure bp is valid to be removed from the list
    if (bp == NULL || GET_ALLOC(HDRP(bp)))
        return;

    // Get the block's root, prev and next
    void *root = get_root(GET_SIZE(HDRP(bp))); 
    void* prev = (void*) GET_PREVP(bp);
    void* next = (void*) GET_NEXTP(bp);

    // Sever the block from the free list first
    SET_PREVP(bp, (size_t) NULL);
    SET_NEXTP(bp, (size_t) NULL);

    if (prev == NULL && next == NULL) { 
        // Case 1: Set root to NULL
        PUT_8B(root, (size_t) NULL);

    } else if (prev != NULL && next == NULL) {
        // Case 2: Set next of previous to be NULL
        SET_NEXTP(prev, (size_t) NULL);

    } else if (prev == NULL && next != NULL){
        /* Case 3: Set previous of next to be NULL,
         root to be pointed to next */
        SET_PREVP(next, (size_t) NULL);
        PUT_8B(root, (size_t) next);

    } else { // prev != NULL && next != NULL
        // Case 4: next and prev point to each other
        SET_PREVP(next, (size_t) prev);
        SET_NEXTP(prev, (size_t) next); 
    }

}

/* 
 * insert_to_free_list - insert block bp into segragated free list by size classes
 *                       Each size class is linked in ascending order
 */
static void insert_to_free_list(void* bp) {
    // Ensure bp is valid
    if (bp == NULL)
        return;

    // Prepare size of current bp and variable for next size
    size_t size = GET_SIZE(HDRP(bp));
    size_t next_size;

    // Prepare root, prev and next to find position of the block
    void* root = get_root(size);
    void* prev = root;
    void* next = (void *) GET_8B(root);
    
    // Sorting to find position of current block
    while (next != NULL) {
        next_size = GET_SIZE(HDRP(next));

        if (next_size >= size) 
            break;
        
        prev = next;
        next = (void*) GET_NEXTP(next);
    }

    // Proper insertion: similar 4 cases as remove_from_free_list
    if (prev == root && next == NULL){
        // Case 1: The only block
        // Set pointer for root
        PUT_8B(root, (size_t) bp);

        dbg_printf("size of bp=%d\n", GET_SIZE(HDRP(bp)));
        // Set pointers for bp
        SET_PREVP(bp, (size_t) NULL);
        SET_NEXTP(bp, (size_t) next);

    } else if (prev != root && next == NULL) {
        // Case 2: The last block
        // Set pointers for bp 
        SET_PREVP(bp, (size_t) prev);
        SET_NEXTP(bp, (size_t) next);

        // Prev block points to bp as next
        SET_NEXTP(prev, (size_t) bp);

    } else if (prev == root && next != NULL) {
        // Case 3: The first block
        // Set pointer for root
        PUT_8B(root, (size_t) bp);

        // Set pointers for bp
        SET_PREVP(bp, (size_t) NULL);
        SET_NEXTP(bp, (size_t) next);

        // Next block points to bp as previous
        SET_PREVP(next, (size_t) bp);

    } else { // prev != root && next != NULL
        // Case 4: The in between block
        // Set pointers for bp
        SET_PREVP(bp, (size_t) prev);
        SET_NEXTP(bp, (size_t) next);

        // Set pointer for bp's prev
        SET_NEXTP(prev, (size_t) bp);

        // Set pointer for bp's next
        SET_PREVP(next, (size_t) bp);

    }
}

/*
 * extend_heap - extend heap with a new free block = words * WSIZE
 */
static void* extend_heap(size_t words) {
    char* bp;
    size_t size;

    dbg_printf("Entered extend_heap\n");

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp)) )); // Free block's header, copy prev_alloc
    PUT(FTRP(bp), GET(HDRP(bp)));           // Free block's footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   // New epilogue's header

    // Unlink the block first
    SET_PREVP(bp, (size_t) NULL); 
    SET_NEXTP(bp, (size_t) NULL);

    return coalesce(bp); // coalesce if the previous block is free.
    // Block will be inserted into free list after coalescing
}

/* coalesce -  Return pointer to coalesced block, folows 4 cases frm textbook
            Combines with free blocks before and/or after current block,
            using 2nd bit to judge if previous is free or not
            Free blocks are removed from the free list, 
            final big free block is then inserted into free list
*/
static void* coalesce(void *bp) {
    dbg_printf("Start of coalesce\n");
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Find the pointers for previous and next blocks
    void* prev_bp = PREV_BLKP(bp);
    void* next_bp = NEXT_BLKP(bp);

    if (prev_alloc && next_alloc) { // Case 1

        // Nothing to be done, ready to insert and return

    } else if (prev_alloc && !next_alloc) { // Case 2: Next block is free
        // Remove next block from free list
        remove_from_free_list(next_bp);

        // Get size of next block
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size += next_size;

        PUT(HDRP(bp), PACK(size, 0b10)); // last 2 bits: 10
        PUT(FTRP(bp), GET(HDRP(bp))); 

    } else if (!prev_alloc && next_alloc) { // Case 3: Prev block is free
        // Remove previous block from free list
        remove_from_free_list(prev_bp);

        // Get size of prev block
        size_t prev_size = GET_SIZE(HDRP(prev_bp));
        size += prev_size;

        // Move bp up to position of prev bp
        bp = prev_bp;

        // Update header of current bp (which is position of prev_bp)
        // last 2 bits: ?0 (follow prev_bp header)
        PUT(HDRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(prev_bp)) ) ); 
        PUT(FTRP(bp), GET(HDRP(bp)) ); // footer copies from header

    } else { // Case 4: Both prev and next blocks are free
        // Remove both from free list
        remove_from_free_list(prev_bp);
        remove_from_free_list(next_bp);
        
        // Get sizes
        size_t prev_size = GET_SIZE(HDRP(prev_bp));
        size_t next_size = GET_SIZE(HDRP(next_bp));
        size +=  prev_size + next_size;

        // Move bp up to position of prev bp
        bp = prev_bp;

        // Update header of current bp (position of prev_bp) with combined size
        // last 2 bits: ?0 (follow prev_bp header)
        PUT(HDRP(prev_bp), PACK(size, GET_PREV_ALLOC(HDRP(prev_bp)) ) );
        PUT(FTRP(prev_bp), GET(HDRP(bp)) );
    }

    // Finally, insert the coalesced block into free list
    insert_to_free_list(bp);
    dbg_printf("End of coalesce\n");
    //mm_checkheap(__LINE__);
    return bp; // Returns pointer to coalesced block
}

/*
 * Initialize - return -1 on error, 0 on success. Creates 10*(8 bytes) spaces
 *               to hold the addresses of the start of 10 class sizes
 *              Final two 8 byte blocks are split into 4 bytes: 
 *              |--Alignment padding--|---Prologue Header---|
 *              |---Prologue Footer---|---Epilogue Header---|
 *              Heap list starts right after prologue header
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(12*DSIZE)) == (void*)-1)
        return -1;
    
    // Create segregated free list
    PUT_8B(heap_listp, (size_t) NULL);           //block size <= 32  
    PUT_8B(heap_listp + (1*DSIZE), (size_t) NULL); //block size 33 - 64
    PUT_8B(heap_listp + (2*DSIZE), (size_t) NULL); //block size 65 - 128
    PUT_8B(heap_listp + (3*DSIZE), (size_t) NULL); //block size 129 - 256
    PUT_8B(heap_listp + (4*DSIZE), (size_t) NULL); //block size 257 - 512
    PUT_8B(heap_listp + (5*DSIZE), (size_t) NULL); //block size 513 - 1024
    PUT_8B(heap_listp + (6*DSIZE), (size_t) NULL); //block size 1025 - 2048
    PUT_8B(heap_listp + (7*DSIZE), (size_t) NULL); //block size 2049 - 4096
    PUT_8B(heap_listp + (8*DSIZE), (size_t) NULL); //block size 4097 - 8192
    PUT_8B(heap_listp + (9*DSIZE), (size_t) NULL); //block size > 8192
    
    // Alignement padding
    PUT(heap_listp + (10*DSIZE), 0); 
    // Prologue header
    PUT(heap_listp + (10*DSIZE + WSIZE), PACK(DSIZE, 0b01)); 
    // Prologue footer, heaplist starts here
    PUT(heap_listp + (11*DSIZE), PACK(DSIZE, 0b01)); 
    // Epilogue header
    PUT(heap_listp + (11*DSIZE + WSIZE), PACK(0, 0b11)); 

    seg_free_listp = heap_listp;
    heap_listp += (11 * DSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= 2*DSIZE)                                          
        asize = MINBLOCKSIZE;                                        
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                  
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);                                 
    return bp;
}

/*
 * free - Free a block
 */
void free (void *bp) {
    if (bp == NULL)
        return;
    //size_t size = GET_SIZE(HDRP(bp));
    void* next_bp = (void*) NEXT_BLKP(bp);

    // Update header and footer of bp
    // 2nd bit unchanged, 1st bit to 0, footer copy header
    PUT(HDRP(bp), ( GET_SIZE(HDRP(bp)) | GET_PREV_ALLOC(HDRP(bp)) ) );
    PUT(FTRP(bp), GET(HDRP(bp)) );

    // Initialise bp (free block) pointers
    SET_PREVP(bp, (size_t) NULL);
    SET_NEXTP(bp, (size_t) NULL);

    // Update next block that previous block is free
    PUT(HDRP(next_bp), ( GET_SIZE(HDRP(next_bp)) | GET_ALLOC(HDRP(next_bp)) ) );

    coalesce(bp);
}

/* find_fit - As list is already in ascending order, just search list
            The first fit will be the best fit
*/
static void* find_fit(size_t asize)
{
    void* root = get_root(asize);

    // As long as root does not hit the prologue header, 
    //  it can search all the class sizes larger than asize class
    while (root != (heap_listp - DSIZE)) {
        // Start from 1st block
        void* bp = (void*) GET_8B(root);

        while (bp != NULL) {
            if (GET_SIZE(HDRP(bp)) >= asize)
                return bp; // Found
            
            // Goes to next block
            bp = (void*) GET_NEXTP(bp);
        }

        // Goes to next class size
        root += DSIZE;
    }
    
    return NULL; /* No fit */
}

/*
 * place - remove the block bp from free list,
 *         and only split if sizeof(remaining part) >= sizeof(smallest block)
 *         Update heaaders and footers respectively
 */
static void place(void* bp, size_t asize)
{
    dbg_printf("Start of place\n");
    //mm_checkheap(__LINE__);
    size_t csize = GET_SIZE(HDRP(bp)); // Original size of block
    remove_from_free_list(bp);
    // Size of remaining block if split occurs
    size_t rsize = csize - asize; 

    if ( rsize >= MINBLOCKSIZE ) { // split
        // Update header: Change size and last bit
        // Second bit is copied
        PUT(HDRP(bp), PACK(asize, (GET_PREV_ALLOC(HDRP(bp)) | 1)) );

        // Block is split, get pointer to next block
        void* new_bp = (void*) NEXT_BLKP(bp);

        // Update header and footer, previous is allocated, self is free
        PUT(HDRP(new_bp), PACK(rsize, 0b10));
        PUT(FTRP(new_bp), PACK(rsize, 0b10));

        // Initialise pointers
        SET_PREVP(new_bp, (size_t) NULL);
        SET_NEXTP(new_bp, (size_t) NULL);

        // Insert new block back into free list
        insert_to_free_list(new_bp);
    }
    else { // don't split
        // Update header: Change size and last bit
        // Second bit is copied
        PUT(HDRP(bp), PACK(csize, (GET_PREV_ALLOC(HDRP(bp)) | 1)) );

        // Find next block
        void* next_bp = (void*) NEXT_BLKP(bp);

        // Update footer of next block that previous block is allocated
        PUT(HDRP(next_bp), ( GET(HDRP(next_bp)) | 0b10 ) );

        // If next block is free, update footer
        if (!GET_ALLOC(HDRP(next_bp)))
            PUT(FTRP(next_bp), GET(HDRP(next_bp)) );
    }
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block. 
 */
void *realloc(void *oldptr, size_t size) {
    /* Copied from mm-naive.c */
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;

}

/*
 * calloc - Allocate the block and set it to zero.
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    /* Copied from mm-naive.c */
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap - Check the invariants in my data structures
 */
void mm_checkheap(int lineno) {
    // Start of heap list
    void *ptr = heap_listp;
    dbg_printf("Entered checkheap\n");

    // Checking the heap
    while (GET_SIZE(HDRP(ptr)) > 0) {
        
        // Check alignment
        if (!aligned(ptr))
            printf("bp %p is not aligned\n", ptr);
        // Check in heap
        if (!in_heap(ptr))
            printf("bp %p is not in heap\n", ptr);
        
        // Check coalescing
        if (!GET_ALLOC(HDRP(ptr)) && !GET_PREV_ALLOC(HDRP(ptr)) )
            printf ("bp %p and previous block are both free\n", ptr);
        if (!GET_ALLOC(HDRP(ptr)) && !GET_ALLOC(HDRP(NEXT_BLKP(ptr))) )
            printf ("bp %p and next block are both free\n", ptr);

        // Check header and footer size match for free block
        // Check for pointer consistency for free block
        if (!GET_ALLOC(HDRP(ptr)) ) {
            if (GET_SIZE(HDRP(ptr)) != GET_SIZE(FTRP(ptr)) )
                printf ("size in free block %p's header and footer does not match\n", ptr);
            
            // If this is the first or last block in the list, continue
            if (GET_NEXTP(ptr)== (size_t) NULL || GET_PREVP(ptr)==(size_t)NULL){
                ptr = NEXT_BLKP(ptr);
                continue;
            }
            // Check pointer consistency
            if (ptr != (void*) GET_PREVP(GET_NEXTP(ptr)) )
                printf("pointer %p mismatch with next block\n", ptr);
            if (ptr != (void*) GET_NEXTP(GET_PREVP(ptr)) )
                printf("pointer %p mismatch with previous block\n", ptr);

        }

        ptr = NEXT_BLKP(ptr);
        
    }
    dbg_printf("out of checkheap while loop\n");
    // Check the segregated free list: correct class size and order
    unsigned int min = 0, max = 0, i = 0;
    for (i = 0; i < 10; i++) {

        // All sizes in bytes
        switch (i){
            case 0:
                min = 0;
                max = 32; 
                break;
            case 1:
                min = 33;
                max = 64; 
                break;
            case 2:
                min = 65;
                max = 128; 
                break;
            case 3:
                min = 129;
                max = 256; 
                break;
            case 4:
                min = 257;
                max = 512; 
                break;
            case 5:
                min = 513;
                max = 1024; 
                break;
            case 6:
                min = 1025;
                max = 2048; 
                break;
            case 7:
                min = 2049;
                max = 4096; 
                break;
            case 8:
                min = 4097;
                max = 8192; 
                break;
            case 9: 
                min = 8193;
                max = (1<<31);
                break;
        }
 
        ptr = seg_free_listp + (i*DSIZE);
        dbg_printf("i=%d\n", i);
       
        ptr = (void*) GET_8B(ptr);
        // If this size class list is empty, continue
        if (ptr == (void*) NULL) 
            continue;
        
        dbg_printf("after continue\n"); 
        
        // Found non-null free list, then traverse it
        while (ptr != (void*) NULL) {
            dbg_printf("inside while loop i=%d max=%d min =%d\n", i, max, min);
            unsigned int fbsize = GET_SIZE(HDRP(ptr));
            unsigned int nxsize = 0;
            dbg_printf("fbsize=%d\n", fbsize);
            if (fbsize > max || fbsize < min)
                printf("Bp %p is in the wrong size class. \n", ptr);

            // Check order
            if (GET_NEXTP(ptr) != (size_t) NULL) {
                nxsize = GET_SIZE(HDRP(GET_NEXTP(ptr)));
                if (fbsize > nxsize)
                    printf("Bp %p is in the wrong order.\n", ptr);
            }
            
            ptr = (void*) GET_NEXTP(ptr);
            dbg_printf("end of while loop 1\n");
        }
        dbg_printf("end of while loop 2\n");
    }

    dbg_printf("End of checkheap\n");
}

