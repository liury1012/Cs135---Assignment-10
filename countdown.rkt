;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname countdown) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
;;
;;***************************
;; Ryan Liu (   )
;; CS 135 Fall 2019
;; Assignmnet 10 Question 2
;;***************************

;; Data Definitions

;; An Operator (Op) is (anyof '+ '- '* '/)
;; A Binary Expression Tree (BET) is one of:
;; * Nat
;; * (list Op BET BET)


;; A tree structure (TrStruct) is one of
;; * empty
;; * (list Nat TrStruct TrStruct)


;; a) ---

;; a (i)

;; (swap i j lst) produces lst with the elements at positions
;; i and j swapped
;; swap: Nat Nat (listof X) -> (listof X)
;; requires: i, j < (length lst)

(define (swap i j lst)
  (cond [(or (empty? lst) (= i j)) lst]         ; no change on lst
        [else
         (local [(define (swap/acc xlst ix)
                   (cond [(empty? xlst) empty]
                         [(= ix i) (cons (list-ref lst j)
                                         (swap/acc (rest xlst) (add1 ix)))]
                         [(= ix j) (cons (list-ref lst i)
                                         (swap/acc (rest xlst) (add1 ix)))]
                         [else (cons (first xlst)
                                     (swap/acc (rest xlst) (add1 ix)))]))
                 ]
           (swap/acc lst 0))]))
                     
;; Tests
(check-expect (swap 0 3 '(0 1 2 3 4 5)) '(3 1 2 0 4 5))
(check-expect (swap 3 0 '(0 1 2 3 4 5)) '(3 1 2 0 4 5))


;; a (ii)

;; Analysis ---
;;
;; One permutation algorithm
;;                                   lst  = '(A B C)                               swap start
;;                    /                  |                   \
;;              swap A A              swap A B              swap A C                     0
;;                  /                    |                      \
;;             '(A B C)               '(B A C)                '(C B A)
;;              A is fixed             B is fixed              C is ficed 
;;               /   \                  /      \                /      \
;;         swap B B  swap B C       swap A A  swap A C      swap B B   swap B A          1
;;            /        \              /         \              /         \
;;      '(A B C)     '(A C B)     '(B A C)     '(B C A)     '(C B A)    '(C A B)
;;      A B fixed    A C fixed     B A fixed    B C fixed   C B fixed   C A fixed
;;
;; The diagram suggests a help function that swaps an element at a position (start)
;; with every elements after that position and then recursively (depth-first) permute the
;; generated lists with increased swap start position (add1 start).
;;
;; Since the wap function needs indexs, the help fucntion takes the target list and a companion index list
;; as its second and thir paramters, beside the swap start position.
;; The swap of elem at start position with every elements at and after the start position can be
;; implemnted naturally by folding right on the index list. Note that swap at the same position (i.e., i = j)
;; do not change ths list.
;; -----------------------------------

;;
;; (generate-permutations lst) consumes a list and produces
;;    the list of permutaions of elements in lst
;; generate-permutations:(listof X) -> (listof (listof X))

(define (generate-permutations lst)
  (local [(define len (length lst))]
    (cond [(<= len 1) (list lst)]        ; (generate-permutations empty) >> '(()) since 0! = 1
          [else
           (local [(define last-ix (sub1 len))
                   (define index-list (build-list len (lambda (i) i)))
                   
                   ;; Nat (lisof X) (listof Nat) -> (listof (listof X)) 
                   (define (permutations start curr-lst ix-lst)
                     (cond [(= start last-ix) (list curr-lst)]
                           [else
                            (foldr (lambda (ix ror)
                                     (append (permutations
                                                 (add1 start)
                                                 (swap start ix curr-lst)
                                                 (rest ix-lst))
                                             ror))
                                     empty
                                     ix-lst)]))   
                   ]
             (permutations 0 lst index-list))])))

;; Tests:                                      
(check-expect (generate-permutations '()) '(()))
(check-expect (generate-permutations '(1)) '((1)))
(check-expect (generate-permutations '(1 2)) '((1 2) (2 1)))                                     
(check-expect (generate-permutations '(1 2 6))
              '((1 2 6) (1 6 2) (2 1 6) (2 6 1) (6 2 1) (6 1 2)))
(check-expect (generate-permutations '(8 1 2 6))
              '((8 1 2 6) (8 1 6 2) (8 2 1 6) (8 2 6 1) (8 6 2 1) (8 6 1 2)
                (1 8 2 6) (1 8 6 2) (1 2 8 6) (1 2 6 8) (1 6 2 8) (1 6 8 2)
                (2 1 8 6) (2 1 6 8) (2 8 1 6) (2 8 6 1) (2 6 8 1) (2 6 1 8)
                (6 1 2 8) (6 1 8 2) (6 2 1 8) (6 2 8 1) (6 8 2 1) (6 8 1 2)))
(check-expect (length (generate-permutations '(1 2 3 4 5 6))) 720)     ; 6! = 720

              
;; a (iii)

;; The ideal is
;;   (generate-tuples lst n) = (gen-products lst (generate-tuples lst (sub1 n))
;;
;; The exit base condition for above mutual recursion shall be n = 0 the smallest Nat.
;;
;; We start with a simple program structures that are easy to understand and then tranform
;; them into shorter program by using abstract list functions.
;;
;; From the examples, we know that the result of generate-tuples is (listof (listof X))
;; So, the signatures of gen-products shall be
;;        (listof X) (listof (listof X)) -> (listof (listof X))
;;
;; The second paremater is a list of list. A simple method for gen-products is to add
;; each element of the first list to every list elements of the second parameter list.
;; So, we get a helper function
;;
;; ;; add-elem: X (lisof (list X)) -> (listof (listof X))
;; ;; Example:
;; (check-expect (add-elem '+ '((+) (-))) '((+ +) (+ -)))
;; (define (add-elem x l-lst)
;;  (cond [(empty? l-lst) empty]
;;        [else (cons (cons x (first l-lst)) (add-elem  x (rest l-lst)))]))   
;;   
;; The definition of add-elem implies that the exit base condtion (generate-tuples lst 0)
;; shall return a list of empty list (list empty) = '(()). Now, we can write both
;; generate-tuples and gen-products.
;;
;; ;; gen-products: (listof X) (listof (listof X) -> (listof (listof X))
;; ;; Example:
;; (check-expect (gen-products '(+ -) '((+) (-))) '((+ +) (+ -) (- +) (- -)))  
;; (define (gen-products lst l-lst)
;;   (cond [(empty? lst) empty]
;;         [else (append (add-elem (first lst) l-lst) (gen-products (rest lst) l-lst))]))
;;
;; ;; generate-tuples: (listof X) Nat -> (listof (listof X))
;; ;; Example
;; (check-expect (generate-tuples '(+ -) 3)
;;               '((+ + +) (+ + -) (+ - +) (+ - -)
;;                 (- + +) (- + -) (- - +) (- - -)))
;; (define (generate-tuples lst n)
;;  (cond [(or (<= n 0) (empty? lst)) '(())]
;;        [else (gen-products lst (generate-tuples lst (sub1 n)))]))

;; We didn't make the helper functions local becasue we want test them individually.
;; According to the assigment requirement, we can make them local and finish this part.
;; However, we want go one step further, eleminate the use of local helper functions.
;;
;; Function add-elem traverses on list l-lst and can be naturally transfromed to a map
;; expression:
;;
;; (check-expect (add-elem '+ '((+) (-))) '((+ +) (+ -)))
;; (define add-elem (lambda (x l-lst) (map (lambda (l) (cons x l)) l-lst)))
;;                  
;; The gen-products assembles the structure of foldr on traversing lst
;; 
;; (check-expect (gen-products '(+ -) '((+) (-))) '((+ +) (+ -) (- +) (- -)))  
;; (define (gen-products lst l-lst)
;;   (foldr (lambda (x ror) (append (map (lambda (l) (cons x l)) l-lst) ror)) empty lst))
;;
;; Finally, eliminate gen-products by replacing l-lst with (generate-tuples lst (sub1 n))
;; ---------


;; (generate-tuples lst n) produces all tuples of length n of
;; elements in lst.
;; generate-tuples: (listof X) Nat -> (listof (listof X))

(define (generate-tuples lst n)
  (cond [(or (<= n 0) (empty? lst)) '(())]
        [else
         (foldr (lambda (x ror)
                  (append (map (lambda (l) (cons x l))
                               (generate-tuples lst (sub1 n)))
                          ror))
                empty
                lst)]))

;; Tests:
(check-expect (generate-tuples '(+) 0) '(()))
(check-expect (generate-tuples '(+) 1) '((+)))
(check-expect (generate-tuples '(+) 2) '((+ +)))
(check-expect (generate-tuples '(+ -) 1) '((+) (-)))
(check-expect (generate-tuples '(+ -) 2) '((+ +) (+ -) (- +) (- -)))
(check-expect (generate-tuples '(+ -) 3)
              '((+ + +) (+ + -) (+ - +) (+ - -)
                (- + +) (- + -) (- - +) (- - -)))
                        


;; a (iv)

;; ---------
;; Analysis
;;
;;  There are three loops"
;;    1. loop on nlon
;;       for each number list (num-lst) from nlon
;;          2. loop on nloop
;;                for each op list (op-lst) from nloop
;;                  3. loop on the TrStuct lst created from num-lst and op-lst
;;                       for each tree stucture ts, create a bet
;;
;; - loop 3 can be implemnted by map on the tree structure lists, it will return a list of bets
;; - loop 2 and list 1 can be implemeted by foldr or foldl to connect (append) the lists of lists
;;
;; Note you shall not use map to connect a list with another list. Map uses cons to add an element
;; to a list.
;;
;;  So the real task is a help function, create-single-bet, which created a bet from a tree structure.
;;  Study carefully the examples, we have following observation:
;;      - the nubmers in the num-lst are placed to the leafs in depth-first (left to right) order
;;      - the operators placed on the internal node depends on the level of the internal nodes
;;
;;  num-list = '(8 6 4 3)   op-lst = '(\ + -)
;;
;; (list 3 empty (list 2 empty (list 1 empty empty)))
;;     3                         \                   root op / (list-ref op-lst 0)
;;    /  \                      /  \
;;        2            >>      8    +                level 1 op +  (list-ref op-lst 1)
;;       / \                      /  \
;;          1                    6    -              level 1 op -  (list-ref op-lst 2)
;;         / \                       / \
;;                                  4   3
;; (list 3 (list 1 empty empty) (list 1 empty empty))
;;        3                    \                                           
;;       /  \                 /  \
;;      1    1       >>      +    +                   both level 1 op = +
;;     / \  / \             / \   / \
;;                         8   6  4  3
;;
;; 
;; (list 3 (list 2 (list 1 empty empty) empty) empty)
;;          3                    \
;;         /  \                 /  \
;;        2          >>        +    3      >> (/ (+  (- 8 6) 4) 2)
;;       / \                  /  \ 
;;      1                   -     4
;;                         / \
;;                        8   6
;;
;; create-single-bet wil be recursively called on the left and righ subtrees. Hence, itshall
;; additionally takes level and number indexs as accumulators. The level index is passed to
;; the calls on subtrees by add1. The problem is number index. As we see from above examples,
;; the numbers used by left-subtree are not a fixed number. It could be 1, 2 or 3.
;; A number we know only after we build the sub-bet from the subtree. Hence, we encode
;; the number index into the returned reult of create-single-bet: (list BET next-number-ix)
;;  

;; ----------------------

;; (create-bets nlon nloop) produces a list of all possible BET based on nlon and nloop.
;; create-bets: (listof (listof Num)) (listof (listof Op)) -> (listof BET)
;; requires: (length nlon) - (length nloop) = 1

(define (create-bets nlon nloop)
  (local [;; create-single-bet: TrStuct (listof Nat) (listof Op) Nat Nat -> (list Bet Nat)
          (define (create-single-bet ts num-lst op-lst num-ix op-lvl)
            (cond [(empty? ts) (list (list-ref num-lst num-ix)     ; leafs - for numbers
                                     (add1 num-ix))]               ; next to be used number
                  [else
                   (local [(define l-subtr (create-single-bet
                                               (second ts)
                                               num-lst op-lst
                                               num-ix (add1 op-lvl)))
                           (define r-subtr (create-single-bet
                                               (third ts)
                                               num-lst op-lst
                                               (second l-subtr) (add1 op-lvl)))
                           ]
                     (list (list (list-ref op-lst op-lvl)   ; the (partially built) bet
                                 (first l-subtr)
                                 (first r-subtr))
                           (second r-subtr)))]))      ; index (in num-list) of the next to be used number
          ]
    (cond [(empty? nloop) empty]
          [else
           (foldr (lambda (num-lst ror-num)              ; traverse on (listof (listof Num)) nlon
                    (append
                       (foldr (lambda (op-lst ror-op)    ; traverse on (listof Op (listof Op)) nloop
                                (append
                                   (map (lambda (ts)     ; traverse on tree structrues created from num-lst and op-lst
                                          (first (create-single-bet ts num-lst op-lst 0 0)))
                                        (create-tree-structure (length op-lst)))
                                   ror-op))
                              empty
                              nloop)
                       ror-num))
                  empty
                  nlon)])))
 
;; Tests:
(check-expect (create-bets  '((8 6)) '((+))) '((+ 8 6)))
(check-expect (create-bets '((8 6 3) (9 6 1)) '((+ -) (* /)))
              '( (+ 8 (- 6 3)) (+ (- 8 6) 3)
                 (* 8 (/ 6 3)) (* (/ 8 6) 3)
                 (+ 9 (- 6 1)) (+ (- 9 6) 1)
                 (* 9 (/ 6 1)) (* (/ 9 6) 1) ))
(check-expect (create-bets '((8 6 4 2)) '((/ + -)))
              '((/ 8 (+ 6 (- 4 2)))
                (/ 8 (+ (- 6 4) 2))
                (/ (+ 8 6) (+ 4 2))
                (/ (+ 8 (- 6 4)) 2)
                (/ (+ (- 8 6) 4) 2)))


;; (create-left-right-pairs n) produces a list of number-pairs indicating the size of
;;   the left and right subtrees for a given total node-count n on a binary tree
;; create-left-right-pairs: Nat -> (listof (list Nat Nat))
;; Example: 
(check-expect (create-left-right-pairs 3) '((2 0) (1 1) (0 2)))
(define (create-left-right-pairs n)                 ; result list have n elements (a b) with a + b = n - 1
  (cond [(= n 0) empty]
        [else (build-list n (lambda (i) (list (- (sub1 n) i) i)))])) ; formula ((n-1) - i) i) i = 0, ... (n-1) 
  
;; Tests
(check-expect (create-left-right-pairs 1) '((0 0)))
(check-expect (create-left-right-pairs 2) '((1 0) (0 1)))
(check-expect (create-left-right-pairs 4) '((3 0) (2 1) (1 2) (0 3)))              


;; --------------------------
;; Analysis: 
;;
;; Look carefully the expect result of (create-tree-structure 3)
;;    (list (list 3 empty (list 2 empty (list 1 empty empty)))         
;;          (list 3 empty (list 2 (list 1 empty empty) empty))          
;;          (list 3 (list 1 empty empty) (list 1 empty empty))       
;;          (list 3 (list 2 empty (list 1 empty empty)) empty)        
;;          (list 3 (list 2 (list 1 empty empty) empty) empty)))       
;; 
;; It is clear that the list elements are create from the left-right-pairs of 3
;;    '((2 0) (1 1) (0 2))
;; The first two list elements are built from from pair (0 2). Their third elements
;; are the tree elements for 2: (list 2 empty (list 1 empty empty))
;;                              (list 2 (list 1 empty empty) empty)
;;
;; So, we have the first helper function, create-tree-from-pair which given a pair
;; (l r), create the list of tree structures built as products of tree structures
;; for number l and r:            
;;  (create-tree-structures l): '(a b)      (create-tree-strcutures r): '(c d)
;;    foldl/foldr on '(a b)        map on '(c d)      
;;                 a  --------- (a c)
;;                              (a d)
;;                 b  --------- (b c)
;;                              (b d)
;; To generate products from two list, we first traverse (foldr or foldl) the
;; list of l. For each element of list l, we tarverse (map) the list of r.
;;
;; ;; Nat (list Nat Nat) -> (listof TrStruct)                                           
;; (define (create-tree-from-pair n lrp)
;;    (foldr (lambda (left ror)
;;            (append (map (lambda (right) (list n left right))
;;                         (create-tree-structure (second lrp)))
;;                    ror))
;;           empty
;;           (create-tree-structure (first lrp)))) 
;;
;; The implementation of create-tree-from-pair indicates that (create-tree-structure 0)
;; shall give (list empty) instead of empty. 
;;  
;; ;; Nat -> (listof TrStruct)                                                                  
;; (define (create-tree-structure n)
;;  (cond [(= n 0) (list empty)]
;;        [else (create-tree-from-pair-list n (create-left-right-pairs n))]))
;;
;; The second help function create-tree-from-pair-list just connect together the lists
;; created for each pair in the left-right pair list. Observing that in the example,
;; the first two tree structres are from the last pair (0 2), we realize that
;; create-tree-from-pair-list shall use fold left foldl:
;;
;; ;; Nat (listof (list Nat Nat)) -> (listof TrStruct)
;; (define (create-tree-from-pair-list n lrp-lst)
;;  (foldl (lambda (lrp ror) (append (create-tree-from-pair n lrp) ror))
;;         empty
;;         lrp-lst))
;;
;; Finally, eliminate the two help functions and get he final version
;; ---------------------------

;; (create-tree-structure n) consumes a natural number n and produces
;;   a list of possible trees that have n internal nodes
;; requires: the node values in each of the tree represent the number of nodes
;; create-tree-structure: Nat -> (listof TrStruct)

(define (create-tree-structure n)
  (cond [(= n 0) (list empty)]
        [else
         (foldl (lambda (lrp ror)
                  (append (foldr (lambda (left ror)
                                   (append (map (lambda (right) (list n left right))
                                                (create-tree-structure (second lrp)))
                                           ror))      ; ror in (left ror)
                                 empty
                                 (create-tree-structure (first lrp)))
                          ror))    ; ror in (lrp ror)
                  empty
                  (create-left-right-pairs n))]))
        
;; Tests
(check-expect (create-tree-structure 2) (list (list 2 empty (list 1 empty empty))
                                              (list 2 (list 1 empty empty) empty)))
(check-expect (create-tree-structure 3)    
              (list (list 3 empty (list 2 empty (list 1 empty empty)))
                    (list 3 empty (list 2 (list 1 empty empty) empty))
                    (list 3 (list 1 empty empty) (list 1 empty empty))
                    (list 3 (list 2 empty (list 1 empty empty)) empty)
                    (list 3 (list 2 (list 1 empty empty) empty) empty)))

;; Note: The notation from the assigmnet instruction do not work.
;;         '(3 empty) >> (list 3 'empty)
;;    (equal? 'empty '()) >> false   (equal? 'empty empty) >> false
;; (check-expect(create-tree-structure 3)
;;             '((3 empty (2 empty (1 empty empty)))
;;               (3 empty (2 (1 empty empty) empty))
;;               (3 (1 empty empty) (1 empty empty))
;;               (3 (2 empty (1 empty empty)) empty)
;;               (3 (2 (1 empty empty) empty) empty)))


;;a (v)

;; (evaluate-bets lobet target) produces a list of all BET from
;; lobet that evaluate to the target value.
;; evaluate-bets: (listof BET) Nat -> (listof BET)

(define (evaluate-bets lobet target)
  (local [(define trans-table (list (list '+ +)
                                    (list '- -)
                                    (list '* *)
                                    (list '/ /)))
          
            ;; find-op: Sym -> (anyof false Str)
          (define (find-op lst sym)
            (cond [(empty? lst) false]
                  [(symbol=? (first (first lst)) sym) (second (first lst))]
                  [else (find-op (rest lst) sym)]))
          
          ; (eval bet)returns a natural number if the result is a non-negative integer
          ;;                  false if result is negative, fractional number, or divided by zero
          ; eval: Bet -> (anyof false Nat)
          (define (eval bet)
            (cond [(number? bet) bet]
                  [else
                   (local [(define op (find-op trans-table (first bet)))]
                     (cond [(false? op) false]
                           [else
                            (local [(define n (eval (second bet)))]                   ; first operand
                              (cond [(false? n) false]                    
                                    [else
                                     (local [(define m (eval (third bet)))]           ; second operand
                                       (cond [(false? m) false]
                                             [else
                                              (cond [(symbol=? (first bet) '/)        ; special for divison 
                                                     (cond [(= m 0) false]      
                                                           [else
                                                            (local [(define ret (/ n m))]
                                                              (cond [(not (integer? ret)) false]  ; not integer result
                                                                    [else ret]))])]
                                                    [else
                                                     (local [(define ret (op n m))]
                                                       (cond [(< ret 0) false]        ; negative intermediate result
                                                             [else ret]))])]))]))]))]))
          ]
    (filter (lambda (bet)
              (local [(define ret (eval bet))]
                (and (not (false? ret)) (= ret target))))
            lobet)))


;; Tests: 
(check-expect (evaluate-bets '((+ (- 7 2) 3)) 6) '())
(check-expect (evaluate-bets (create-bets (generate-permutations '(2 4 8))
                                          (generate-tuples '(+ - *) 2))
                             2)
              '((- 8 (+ 4 2)) (- (- 8 4) 2) (- 8 (+ 2 4)) (- (- 8 2) 4)))
;; (check-expect (length (evaluate-bets (create-bets
;;                                      (generate-permutations '(1 5 7 10 25))
;;                                      (generate-tuples '(+ - * /) 4))
;;                                     135))
;;              164)   


;; a (vi)

;; (countdown-numbers lon target) produces a BET using the numbers in lon
;; that evaluates to target, or false if no such BET exists.
;; countdown-numbers: (listof Nat) Nat -> (anyof BET false)

(define (countdown-numbers lon target)
  (local [(define len (length lon))]
    (cond [(<= len 1) false]
          [else
           (local [(define bet-lst (evaluate-bets
                                      (create-bets
                                        (generate-permutations lon)
                                        (generate-tuples '(+ - * /) (sub1 (length lon))))
                                      target))]
            (cond [(empty? bet-lst) false]
                  [else (first bet-lst)]))])))
                           
;; Test
(check-expect (countdown-numbers '(1 5 7 10 25) 135) '(+ (* (+ (- 5 1) 7) 10) 25))

;;
;; Welcome to DrRacket, version 7.4 [3m].
;; Language: Intermediate Student with lambda; memory limit: 512 MB.
;; All 26 tests passed!
;;
