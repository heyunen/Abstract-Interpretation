#lang racket
(require "pmatch.rkt")

;;; helper functions
(define (union set1 set2)
  (cond
    ((eq? set1 null) set2)
     ((eq? set2 null) set1)
     (else (if (not (memv (car set1) set2))
                       (cons (car set1) (union (cdr set1) (remv (car set1) set2)))
                       (union (cdr set1) set2)))))

(define set-difference
  (lambda (set1 set2)
    (cond
      ((null? set1) '())
      ((null? set2) set1)
      (else (set-difference (filter (lambda (x) (not (eq? x (car set2)))) set1) (cdr set2))))))

(define (unique-free-vars exp)
  (pmatch exp
          [`,x (guard (symbol? x)) `(,x)]
          [`(lambda (,x) ,body)
           (remv x (unique-free-vars body))]
          [`(,rator,rand)
           (union (unique-free-vars rator) (unique-free-vars rand))]))

;;;
(define empty-env
  (lambda ()
    (lambda (y)
      (error 'interp "unbound identifier. ~s" y))))

(define extend-env
  (lambda (var val env)
    `((,var . ,val) . ,env)))

(define apply-env
  (lambda (env var)
    (cond
      [(assq var env) => cdr]
      [else (error 'env "unbound variable. ~s" var)])))

(define closure
  (lambda (x body env)
    `(closure ,x ,body ,env)))

(define apply-closure
  (lambda (closure arg)
    (pmatch closure
      [`(closure ,x ,body ,env)
       (value-of body (extend-env x arg env))])))

;;; call-by-value interpreter
(define value-of
  (lambda (exp env)
    (pmatch exp
      [`,n (guard (number? n)) n]
      [`,b (guard (boolean? b)) b]
      [`,x (guard (symbol? x)) (apply-env env x)]
      [`(zero? ,n) (zero? (value-of n env))]
      [`(+ ,e1 ,e2) (+ (value-of e1 env) (value-of e2 env))]
      [`(- ,e1 ,e2) (- (value-of e1 env) (value-of e2 env))]
      [`(* ,e1 ,e2) (* (value-of e1 env) (value-of e2 env))]
      [`(if ,test ,conseq ,alt) (if (value-of test env)
                                    (value-of conseq env)
                                    (value-of alt env))]
      [`(lambda (,formals) ,body) (closure formals body env)]
      [`(,rator ,rand) (apply-closure (value-of rator env)
                                      (value-of rand env))])))

;;;
(define Ds-zero?
  (lambda (x)
    (pmatch x
            [`bottom `bottom]
            [`,x (guard (integer? x)) (zero? x)]
            [else `top])))

(define Ds-plus
  (lambda (x y)
    (pmatch `(,x ,y)
            [`(bottom ,y) `bottom]
            [`(,x bottom) `bottom]
            [`(,x ,y) (guard (integer? x) (integer? y))
                      (cond
                        [(or (zero? x) (zero? y)) (+ x y)]
                        [(= x y) x]
                        [else `top])]
            [else `top])))

(define Ds-minus
  (lambda (x y)
    (pmatch `(,x ,y)
            [`(bottom ,y) `bottom]
            [`(,y bottom) `bottom]
            [`(,any ,y) (guard (integer? y)) (Ds-plus any (- y))]
            [else `top])))

(define Ds-times
  (lambda (x y)
    (pmatch `(,x ,y)
            [`(bottom ,y) `bottom]
            [`(,x bottom) `bottom]
            [`(,x ,y) (guard (integer? x) (integer? y)) (* x y)]
            [else `top])))

(define Ds-int
  (lambda (x)
    (cond
      [(positive? x) 1]
      [(negative? x) -1]
      [else 0])))

(define Ds-bool
  (lambda (x)
    `bottom))

(define Di-if
  (lambda (eval)
    (lambda (test-exp then-exp else-exp env)
      (if (eval test-exp env)
          (eval then-exp env)
          (eval else-exp env)))))

(define potentially-apply-procedure
  (lambda (eval)
    (lambda (proc args)
      (pmatch proc
              [`(closure ,formals ,body ,env)
               (eval body (extend-env formals args env))]
              [else (error `potentially-apply-procedure
                           "Cannot apply closureL ~s" proc)]))))

(define Di-apply-hov potentially-apply-procedure)

(define **hov-cache** '())

(define cache-maker
  (lambda (binary-predicate? not-found-value-constructor)
    (let ([cache `()])
      (lambda (target)
        (letrec
            ([lookup
              (lambda (table)
                (cond
                  [(null? table)
                   (let ([value (not-found-value-constructor target)])
                     (set! cache (cons `(,target . ,value) cache))
                     value)]
                  [(binary-predicate? target (caar table)) (cdar table)]
                  [else (lookup (cdr table))]))])
          (lookup cache))))))

(define initialize-hov-cache
  (lambda ()
    (set! **hov-cache** (cache-maker Di-closure-equiv? (lambda (target) target)))))

(define Di-closure
  (lambda (closure)
    (**hov-cache** closure)))

(define Di-closure-equiv?
  (lambda (cl-x cl-y)
    (pmatch `(,cl-x ,cl-y)
            [`((closure ,formals-x ,body-x ,env-x)
              (closure ,formals-y ,body-y ,env-y))
             (and
              (eq? body-x body-y)
              (andmap
               (lambda (var)
                 (Di-equiv? (apply-env env-x var) (apply-env env-y var)))
               (set-difference (unique-free-vars body-x) formals-x)))])))

(define Di-equiv?
  (lambda (x y)
    (pmatch `(,x ,y)
            [`(,x ,y) (guard (integer? x) (integer? y)) (= x y)]
            [`((closure ,formals-x ,body-x ,env-x)
              (closure ,formals-y ,body-x ,env-x))
             (Di-closure-equiv? x y)]
            [else #f])))

(define potentially-recursive-eval-maker
  (lambda (D-int D-bool D-zero? D-plus D-minus D-times D-if D-closure D-apply-hov)
    (lambda (eval)
      (lambda (exp env)
        (pmatch exp
                [`,int (guard (number? int)) (D-int int)]
                [`,bool (guard (boolean? bool)) (D-bool bool)]
                [`,var (guard (symbol? var)) (apply-env env var)]
                [`(zero? ,e1) (D-zero? (eval e1 env))]
                [`(+ ,e1 ,e2) (D-plus (eval e1 env) (eval e2 env))]
                [`(- ,e1 ,e2) (D-minus (eval e1 env) (eval e2 env))]
                [`(* ,e1 ,e2) (D-times (eval e1 env) (eval e2 env))]
                [`(if ,test-exp ,then-exp ,else-exp) ((Di-if eval) test-exp then-exp else-exp env)]
                [`(lambda (,formals) ,body) (Di-closure `(closure ,formals ,body ,env))]
                [`(,rator ,rand) ((Di-apply-hov eval) (eval rator env) (eval rand env))])))))

(define fix
  (lambda (potentially-recursive-function)
    (letrec
        ([function
          (potentially-recursive-function
           (lambda args
             (apply function args)))])
      function)))

(define potentially-recursive-eval
  (potentially-recursive-eval-maker
   Ds-int Ds-bool Ds-zero? Ds-plus Ds-minus Ds-times Di-if Di-closure Di-apply-hov))

;;; tests
(define potentially-recursive-factorial
  (lambda (factorial)
    (lambda (n)
      (if (zero? n) 1 (* n (factorial (- n 1)))))))

(let ([factorial (fix potentially-recursive-factorial)])
  (factorial 4))

(define test1 `((lambda (x) (+ x x)) (* 3 4)))

(let ([interp (fix potentially-recursive-eval)])
  (begin
    (initialize-hov-cache)
    (interp test1 (empty-env))))

(value-of test1 (empty-env))