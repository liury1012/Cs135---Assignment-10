;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname travel-map) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
;;
;;***************************
;; Ryan Liu (   )
;; CS 135 Fall 2019
;; Assignmnet 10 Question 1
;;***************************
 
(define southern-ontario
  '( (Brantford ((Hamilton 30)))
     (Cambridge ((Brantford 30) (Hamilton 45) (London 70) (TO 80)))
     (Guelph ((Cambridge 30) (TO 80)))
     (Hamilton ())
     (London ((Brantford 70)))
     (KW ((Cambridge 30) (Guelph 35) (Stratford 40)))
     (Stratford ((London 50)))
     (TO ((Hamilton 60)))
   ))


;;(paths-from node map) returns the list of Neighbour
;;      for a Node node on the Map map
;;      returns empty if the node is not included on map
;; paths-from: Node Map -> (listof Neighbour)))
;; Example:
(check-expect (paths-from 'KW southern-ontario) '((Cambridge 30) (Guelph 35) (Stratford 40)))

(define (paths-from node map)
  (cond [(empty? map) empty]
        [(symbol=? node (first (first map))) (second (first map))]
        [else (paths-from node (rest map))])) 


;; (a)

;; (travel-time src dest map) returns the time required from Node src
;;    to Node dest follow a valid path on Map map;
;;    returns false if there no valid path from 
;; travel-time: Node Node Map -> (anyof false Nat)

(define (travel-time src dest map)
  (cond [(symbol=? src dest) 0]
        [(empty? map) false]
        [else
         (local [;; traverl-time/acc: Nat (listof Neighbour) -> (anyof false Nat)
                 (define (travel-time/acc acc-dur nb-list)
                   (cond [(empty? nb-list) false]
                         [else
                            (cond [(symbol=? dest (first (first nb-list)))                   ; find the destitation
                                   (+ acc-dur (second (first nb-list)))]
                                  [else                                                      ; depth-first search
                                    (local [(define r-fst (travel-time/acc                   ; from the first neighbour              
                                                             (+ acc-dur (second (first nb-list)))
                                                             (paths-from (first (first nb-list)) map)))]
                                      (cond [(not (false? r-fst)) r-fst]                     ; find the time
                                            [else                                            ; from next neighbour  
                                             (travel-time/acc acc-dur (rest nb-list))]))])])) 
                 ]
           (travel-time/acc 0 (paths-from src map)))]))
                                                                                                              
;;
;; Tests: treval-time does depth-first search
;;
(check-expect (travel-time 'KW 'Cambridge southern-ontario) 30)                                            
(check-expect (travel-time 'Guelph 'Hamilton southern-ontario) 90)
; travel time for '(Guelph Cambridge Brantford Hamilton)

(check-expect (travel-time 'KW 'TO southern-ontario) 110)
; travel time for '(KW Cambridge TO)

(check-expect (travel-time 'No 'KW southern-ontario) false)
(check-expect (travel-time 'TO 'KW southern-ontario) false)


;; (b)  

;; (all-paths src dest map) returns the list of paths from src to dest on the Map map
;;     a path is a list of Sym thet lead from src to dest on the map
;; all-paths: Node Node Map -> (listof (cons Node (listof Node)))

(define (all-paths src dest map)
  (cond [(or (empty? map) (symbol=? src dest)) empty]
        [else
         (local [;; all-paths/acc: (listof Node) (listof Neighbour) -> (listof (listof Node))
                 (define (all-paths/acc prnt-path nb-list)
                   (cond [(empty? nb-list) empty]
                         [else
                          (local [(define curr-path (append prnt-path
                                                            (list (first (first nb-list)))))]
                            (cond [(symbol=? dest (first (first nb-list)))                   ; find the destitation
                                   (cons curr-path (all-paths/acc
                                                      prnt-path
                                                      (rest nb-list)))]
                                  [else                                                      ; depth-first search
                                    (append (all-paths/acc
                                               curr-path
                                               (paths-from (first (first nb-list)) map))
                                            (all-paths/acc
                                               prnt-path
                                               (rest nb-list)))]))]))                  
                ]
           (all-paths/acc (list src) (paths-from src map)))]))

(check-expect (all-paths 'Stratford 'Guelph southern-ontario) empty)
(check-expect (all-paths 'No 'Guelph southern-ontario) empty)
(check-expect (all-paths 'Guelph 'No southern-ontario) empty)
(check-expect(all-paths 'Guelph 'Hamilton southern-ontario)
             '((Guelph Cambridge Brantford Hamilton)
               (Guelph Cambridge Hamilton)
               (Guelph Cambridge London Brantford Hamilton)
               (Guelph Cambridge TO Hamilton)
               (Guelph TO Hamilton)))


;; (c)

;;(all-travel-times src dest map) returns the list of labled paths from src to dest on the Map map;
;;     A labled path is a pair of time and a list of Sym that lead from src to dest on the map
;; all-travel-times: Node Node Map -> (listof (list Nat (cons Node (listof Node))))
(define (all-travel-times src dest map)
  (cond [(or (empty? map) (symbol=? src dest)) empty]
        [else
         (local [;; all-paths/acc: (listof Node) (listof Neighbour) -> (listof (listof Node))
                 (define (all-times/acc prnt-path prnt-dur nb-list)
                   (cond [(empty? nb-list) empty]
                         [else
                          (local [(define curr-dur (+ prnt-dur (second (first nb-list))))
                                  (define curr-path (append prnt-path
                                                            (list (first (first nb-list)))))]
                            (cond [(symbol=? dest (first (first nb-list)))                   ; find the destitation
                                   (cons (list curr-dur curr-path)
                                         (all-times/acc prnt-path prnt-dur
                                                        (rest nb-list)))]
                                  [else                                                      ; depth-first search
                                    (append (all-times/acc
                                               curr-path curr-dur
                                               (paths-from (first (first nb-list)) map))
                                            (all-times/acc
                                               prnt-path prnt-dur
                                               (rest nb-list)))]))]))                  
                ]
           (all-times/acc (list src) 0 (paths-from src map)))]))


;; Tests:
(check-expect (all-travel-times 'Guelph 'Hamilton southern-ontario)
              '((90 (Guelph Cambridge Brantford Hamilton))
                (75 (Guelph Cambridge Hamilton))
                (200 (Guelph Cambridge London Brantford Hamilton))
                (170 (Guelph Cambridge TO Hamilton))
                (140 (Guelph TO Hamilton))))
(check-expect (all-travel-times 'Stratford 'Guelph southern-ontario) empty)
