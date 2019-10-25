#lang racket
;;(error "duplicate") if a function has duplicate names
;; amongst the parameters and local variables
;; or there are duplicate function names
;;(error "arguments") if the number of arguments in an application
;; does not match the number of parameters in a function
;;(error "return") if the last statement is not a return statement
;; a program now is a sequence of functions.
;; if there is a main function, the function is applied with no arguments
;; to run the program
;; a function produce an integer value via return stmt

(provide compile-simp)

(define func-name 'f0)

(define func-table (make-hash))

(define vset (mutable-set))

(define (func-lookup name)
  (hash-ref func-table name #f))

(define (add-vset v)
  (if (set-member? vset v)
      (error "duplicate")
      (set-add! vset v)))



(define (op-trans op)
  (cond
    [(symbol=? op '+) 'add]
    [(symbol=? op '-) 'sub]
    [(symbol=? op '*) 'mul]
    [(symbol=? op 'div) 'div]
    [(symbol=? op 'mod) 'mod]
    [true (error "wrong operator!")]))

(define (bool-trans bool)
  (cond
    [(symbol=? bool '=) 'equal]
    [(symbol=? bool '>) 'gt]
    [(symbol=? bool '<) 'lt]
    [(symbol=? bool '>=) 'ge]
    [(symbol=? bool '<=) 'le]
    [(symbol=? bool 'and) 'land]
    [(symbol=? bool 'or) 'lor]
    [(symbol=? bool 'not) 'lnot]
    [true (error "wrong bool!")]))

(define (make-label label)
  (string->symbol (string-append (symbol->string func-name) "LABEL" (number->string label))))

(define (make-var name)
  (string->symbol (string-append (symbol->string func-name) "VAR" (symbol->string name))))

(define (make-const name)
  (string->symbol (string-append (symbol->string func-name) "CONST" (symbol->string name))))


(define (hash-add tb key value)
  (if (hash-has-key? tb key)
      (error "duplicate")
      (hash-set! tb key value)))

(define (set-func-table program)
  (match program
    [(list (list 'fun (list (? symbol? func-name) (? symbol? args) ...) _)
           rst ...)
     (hash-add func-table func-name (length args))
     (set-func-table rst)]
    [(? empty?) (void)]))

(define main-func
  '(fun (main-func)
        (vars []
              (Cequal (Cargs main) 0 (main) (skip))
              Chalt
              stop)))

(define (cp-prog program primp)
  (match program
    [(list (list 'fun
                 (list (? symbol? name) args ...)
                 (list 'vars (list vars ...) stmts ...))
           rst ...)
     (set! func-name name)
     (set! vset (mutable-set))
     (match-let* ([primp0
                   (list* (list 'add 'SP 'SP (make-const 'ssize))
                          (list 'label func-name)
                          primp)]
                  [(list primp1 sizec1) (cp-vars vars primp0 1)]
                  [(list primp2 sizec2 _) (cp-stmt stmts primp1 sizec1 0)]
                  [(list primp3 sizec3) (cp-args (reverse args) primp2 sizec2)]
                  [primp4 (list*
                           (list 'const (make-const 'ssize) (+ 1 sizec3))
                           (list 'const (make-const 'rval) (- 0 (add1 sizec3)))
                           (list 'const (make-const 'raddr) (- sizec3))
                           primp3)])
       (cp-prog rst primp4))]
    [(? empty?) (reverse (list* (list 'data 'STACK 0) (list 'data 'SP 'STACK) primp))]))


(define (cp-args args primp arg-count)
  (cond
    [(empty? args) (list primp arg-count)]
    [true (define arg (car args))
          (add-vset arg)
          (cp-args (cdr args) (cons (list 'const (make-var arg) (- 0 arg-count)) primp)
                   (add1 arg-count))]))


(define (cp-vars vars primp var-count)
  (cond
    [(empty? vars) (list primp var-count)]
    [true (define name-val (car vars))
          (define name (car name-val))
          (define val (second name-val))
          (add-vset name)
          (cp-vars (cdr vars)
                   (cons (list 'move (list (make-var name) 'SP) val)
                         (cons (list 'const (make-var name) (- 0 var-count)) primp))
                   (add1 var-count))]))

(define (cp-stmt stmts primp tmp-count lb-count)
  (cond
    [(empty? stmts) (error "return")]
    [(equal? (list 'skip) (car stmts))
     (cp-stmt (cdr stmts) primp tmp-count lb-count)]
    [true
     
     (match stmts
       
       [(list (list 'print (? string? str)) rst ...)
        (cp-stmt rst (cons (list 'print-string str) primp) tmp-count lb-count)]
       
       [(list (list 'print aexp) rst ...)
        (match-let* ([(list aexp0 primp0 tmp-count0) (cp-aexp aexp primp tmp-count)])
          (cp-stmt rst (cons (list 'print-val aexp0) primp0) tmp-count0 lb-count))]
       
       [(list (list 'set (? symbol? name) aexp) rst ...)
        (match-let* ([(list aexp0 primp0 tmp-count0) (cp-aexp aexp primp tmp-count)])
          (cp-stmt rst (cons (list 'move (list (make-var name) 'SP) aexp0) primp0)
                   tmp-count0 lb-count))]
       
       [(list (list 'seq stms ...) rst ...)
        (cp-stmt (append stms rst) primp tmp-count lb-count)]
       
       [(list (list 'iif bexp stmt1 stmt2) rst ...)
        (match-let* ([lb0 (make-label lb-count)]
                     [lb1 (make-label (add1 lb-count))]
                     [(list bexp0 primp0 tmp-count0)
                      (cp-bexp bexp primp tmp-count)]
                     [primp00
                      (cons (list 'branch bexp0 lb0) primp0)]
                     [(list primp1 tmp-count1 lb-count1)
                      (cp-stmt (list stmt2 'stop) primp00 tmp-count0 (+ 2 lb-count))]
                     [primp11
                      (cons (list 'label lb0) (cons (list 'jump lb1) primp1))]
                     [(list primp2 tmp-count2 lb-count2)
                      (cp-stmt (list stmt1 'stop) primp11 tmp-count1 lb-count1)]
                     [primp22 (cons (list 'label lb1) primp2)])
          (cp-stmt rst primp22 tmp-count2 lb-count2))]
       
       [(list (list 'while cond body ...) rst ...)
        (match-let* ([lb0 (make-label lb-count)]
                     [ifbody
                      (list 'iif cond
                            (append (cons 'seq body) (list (list 'jump lb0)))
                            (list 'skip))]
                     [(list primp0 tmp-count0 lb-count0)
                      (cp-stmt (list ifbody 'stop)
                               (cons (list 'label lb0) primp)
                               tmp-count (add1 lb-count))])
          (cp-stmt rst primp0 tmp-count0 lb-count0))]
       
       [(list (and stmt (list (or 'label 'jump) _)) rst ...)
        (cp-stmt rst (cons stmt primp) tmp-count lb-count)]
       
       [(list (list 'return aexp))
        (cp-stmt (list (list 'return aexp) 'stop) primp tmp-count lb-count)]
       
       [(list (list 'return aexp) rst ...)
        (match-let* ([(list aexp0 primp0 tmp-count0) (cp-aexp aexp primp tmp-count)]
                     [newstmt (list* (list 'jump (list 1 'SP))
                                     (list 'sub 'SP 'SP (make-const 'ssize))
                                     (list 'move (list (make-const 'rval) 'SP) aexp0)
                                     primp0)])
          (cp-stmt rst newstmt tmp-count0 lb-count))]
       
       [(list (list 'Cequal x y thn els) rst ...)
        (match-let* ([(list x0 _ tmp-count0) (cp-aexp x empty 0)]
                     [(list y0 _ tmp-count1) (cp-aexp y empty 0)])
          (cp-stmt (cons (if (equal? x0 y0) thn els) rst) primp tmp-count lb-count))]
       
       [(list (and call (list (? symbol?) _ ...)) rst ...)
        (match-let* ([(list _ primp0 tmp-count0) (cp-aexp call primp tmp-count)])
          (cp-stmt rst primp0 tmp-count0 lb-count))]
       
       [(list 'Chalt rst ...) (cp-stmt rst (cons (list 'halt) primp) tmp-count lb-count)]
       
       [(list 'stop) (list primp tmp-count lb-count)])]))

(define (op? op)
  (or (equal? op '+) (equal? op '-) (equal? op '*) (equal? op 'div)
      (equal? op 'mod)))

(define (bool? bool)
  (or (equal? bool '=) (equal? bool '>) (equal? bool '<)
      (equal? bool '>=) (equal? bool '<=)))

(define (arg-trans args primp tmp-c arg-c)
  (cond
    [(empty? args) (list primp tmp-c)]
    [true (define aexplst (cp-aexp (car args) primp tmp-c))
          (define arg0 (car aexplst))
          (define primp0 (second aexplst))
          (define tmp-c0 (third aexplst))
          (arg-trans (cdr args)
                     (cons (list 'move (list arg-c 'SP) arg0) primp0)
                     tmp-c0 (add1 arg-c))]))


(define (cp-aexp aexp primp tmp-c)
  (match aexp
    [(list 'Cargs func-name) (list (hash-ref func-table func-name -1) primp tmp-c)]
    [(? number? num) (list num primp tmp-c)]
    [(? symbol? id) (list (list (make-var id) 'SP) primp tmp-c)]
    [(list (? op? op) x y)
     (match-let* ([(list aexp0 primp0 tmp-c0) (cp-aexp x primp tmp-c)]
                  [(list aexp1 primp1 tmp-c1) (cp-aexp y primp0 tmp-c0)]
                  [tmp (list (- 0 tmp-c1) 'SP)]
                  [new-stmt (cons (list (op-trans op) tmp aexp0 aexp1) primp1)])
       (list tmp new-stmt (add1 tmp-c1)))]
    [(list (? symbol? calling) args ...)
     (define req-arg (func-lookup calling))
     (when (not req-arg) (error "undefined"))
     (unless (= (length args) req-arg) (error "arguments"))
     (match-let* ([tmp (list (- tmp-c) 'SP)]
                  [(list primp0 tmp-c0) (arg-trans args primp tmp-c 2)]
                  [newstmt (list* (list 'move tmp (list 0 'SP))
                                  (list 'jsr (list 1 'SP) calling) primp0)])
       (list tmp newstmt (add1 tmp-c)))]))


(define (cp-bexp bexp primp tmp-c)
  (match bexp
    ['true (list #t primp tmp-c)]
    ['false (list #f primp tmp-c)]
    
    [(list (? bool? bool) x y)
     (match-let* ([(list x0 primp0 tmp-c0) (cp-aexp x primp tmp-c)]
                  [(list y0 primp1 tmp-c1) (cp-aexp y primp0 tmp-c0)]
                  [tmp (list (- 0 tmp-c1) 'SP)]
                  [new-stmt (cons (list (bool-trans bool) tmp x0 y0) primp1)])
       (list tmp new-stmt (add1 tmp-c1)))]
    
    [(list 'not x)
     (match-let* ([(list bexp0 primp0 tmp-c0) (cp-bexp x primp tmp-c)]
                  [tmp (list (- 0 tmp-c0) 'SP)]
                  [new-stmt (cons (list 'lnot tmp bexp0) primp0)])
       (list tmp new-stmt (add1 tmp-c0)))]
    
    [(list (and bool (or 'and 'or)) fir)
     (match-let* ([(list fir0 primp0 tmp-c0) (cp-bexp fir primp tmp-c)]
                  [tmp (list (- 0 tmp-c0) 'SP)]
                  [newstmt
                   (if (symbol=? bool 'and)
                       (cons (list 'land tmp fir0 #t) primp0)
                       (cons (list 'lor tmp fir0 #f) primp0))])
       (list tmp newstmt (add1 tmp-c0)))]
    
    [(list (and bool (or 'and 'or)) fir sec ...)
     (match-let* ([(list fir0 primp0 tmp-c0) (cp-bexp fir primp tmp-c)]
                  [(list sec0 primp1 tmp-c1) (cp-bexp (cons bool sec) primp0 tmp-c0)]
                  [tmp (list (- 0 tmp-c1) 'SP)]
                  [new-stmt (cons (list (if (symbol=? bool 'and) 'land 'lor) tmp fir0 sec0) primp1)])
       (list tmp new-stmt (add1 tmp-c1)))]))

(define (compile-simp program)
  (set! func-table (make-hash))
  (set-func-table program)
  (cp-prog (cons main-func program) empty))

















  
    








  













      





