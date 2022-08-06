#lang racket

(require "util.rkt")

;;; struct definitions

(struct Program
  [info expr]
  #:transparent)

(struct Var
  [var]
  #:transparent)

(struct Let
  [var rhs body]
  #:transparent)

(struct Prim
  [op args]
  #:transparent)

(struct Int
  [int]
  #:transparent)

(struct CProgram
  [info label->tail]
  #:transparent)

(struct Return
  [expr]
  #:transparent)

(struct Seq
  [stmt tail]
  #:transparent)

(struct Assign
  [var expr]
  #:transparent)

(struct X86Program
  [info blocks]
  #:transparent)

(struct Block
  [info instrs]
  #:transparent)

(struct Instr
  [name args]
  #:transparent)

(struct Imm
  [value]
  #:transparent)

(struct Reg
  [name]
  #:transparent)

(struct Deref
  [reg offset]
  #:transparent)

(struct Callq
  [target arity]
  #:transparent)

(struct Retq
  []
  #:transparent)

(struct Jmp
  [target]
  #:transparent)

(define example-prog
  (Program '() (Let 'a (Int 52) (Prim '+ (list (Var 'a) (Prim '- (list (Int 52))))))))

(define (uniquify-expr e [env '()])
  (match e
    [(Var x) (Var (dict-ref env x))]
    [(Int n) (Int n)]
    [(Let x e body)
     (let* ([new-var (gensym)]
            [new-env (dict-set env x new-var)])
       (Let new-var (uniquify-expr e env) (uniquify-expr body new-env)))]
    [(Prim op es)
     (Prim op (map (λ (e)
                     (uniquify-expr e env)) es))]))

(define (uniquify p)
  (match p
    [(Program '() e) (Program '() (uniquify-expr e))]))

;; rco-atom (prim + ((let x (int 10) (var x)) (int 32)))
;; 
;; rco-atom : expr -> atom * alist
(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Let x e body)
     (define new-var (gensym))
     (define processed-e (rco-expr e))
     (define processed-body (rco-expr body))
     (values (Var new-var) (list (cons x processed-e)
                                 (cons new-var processed-body)))]
    [(Prim op es)
     (define new-var (gensym))
     (define-values (atomified-es vars) (for/fold ([atoms '()]
                                                   [vars '()])
                                                  ([e es])
                                          (define-values (a vs) (rco-atom e))
                                          (values (append atoms (list a))
                                                  (append vars vs))))
     (values (Var new-var) (dict-set vars new-var (Prim op atomified-es)))]))

;; rco-expr : expr -> expr
(define (rco-expr e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x e body) (Let x (rco-expr e) (rco-expr body))]
    [(Prim op es)
     (define atom->vars (map (λ (e)
                               (define-values (atom vars) (rco-atom e))
                               (cons atom vars)) es))
     (define atoms (map car atom->vars))
     (define vars (apply append (map cdr atom->vars)))
     (define (letify-prim [vs vars])
       (cond
         [(empty? vs) (Prim op atoms)]
         [else
          (define v (first vs))
          (define rest-vs (rest vs))
          (define-values (var expr) (values (car v)
                                            (cdr v)))
          (Let var expr (letify-prim rest-vs))]))
     (letify-prim vars)
     ]))

(define (collect-locals->types p)
  (match p
    [(Program '() e)
     (define locals->types (collect-locals->types e))
     (Program (list (cons 'locals->types locals->types)) e)]
    [(Let x rhs body)
     (define rhs-locals (collect-locals->types rhs))
     (define body-locals (collect-locals->types body))
     (append (list (cons x 'Integer))
             rhs-locals
             body-locals)]
    [_ '()]))

(define (remove-complex-opera* p)
  (match p
    [(Program '() e) (Program '() (rco-expr e))]))

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate-assign x rhs (explicate-tail body))]
    [(Prim op es) (Return (Prim op es))]))

(define (explicate-assign var e cont)
  (match e
    [(Var x) (Seq (Assign (Var var) (Var x)) cont)]
    [(Int n) (Seq (Assign (Var var) (Int n)) cont)]
    [(Let x rhs body)
     (define new-cont (explicate-assign var body cont))
     (explicate-assign x rhs new-cont)]
    [(Prim op es) (Seq (Assign (Var var) (Prim op es)) cont)]))

(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (explicate-tail body))]))

(define (si-atom atom)
  (match atom
    [(Var x) (Var x)]
    [(Int n) (Imm n)]))

(define (si-stmt stmt)
  (match-define (Assign x expr) stmt)
  (match expr
    [(Prim op es)
     (define new-stmt (Prim op (map si-atom es)))
     (match new-stmt
       [(Prim '+ (list arg1 arg2))
        (cond
          ;; handling when one of the arguments     
          ;; is the same as the variable assigned to
          [(eq? arg1 x) (list (Instr 'addq (list arg1 x)))] 
          [(eq? arg2 x) (list (Instr 'addq (list arg2 x)))] 
          [else (list (Instr 'movq (list arg1 x))
                      (Instr 'addq (list arg2 x)))])]
       [(Prim '- (list arg)) (list (Instr 'movq (list arg x))
                                   (Instr 'negq (list x)))]
       [(Prim 'read '()) (list (Callq 'read_int 0)
                               (Instr 'movq (list (Reg 'rax) x)))])]
    [_ (list (Instr 'movq (list (si-atom expr) x)))]))

(define (si-tail tail)
  (match tail
    [(Return expr)
     (define assign-to-rax (si-stmt (Assign (Reg 'rax) expr)))
     (define conclusion (list (Jmp 'conclusion)))
     (append assign-to-rax conclusion)]
    [(Seq stmt tail)
     (define new-stmt (si-stmt stmt))
     (define new-tail (si-tail tail))
     (append new-stmt new-tail)]))

(define (select-instructions p)
  (match p
    [(CProgram info body) (X86Program info (list (cons 'start (Block '() (si-tail body)))))]))

(define (type->size type)
  (match type
    ['Integer 8]))

(define (collect-locals->homes locals->types [offset 0])
  (cond
    [(empty? locals->types) (values '() (if (zero? (modulo offset 16))
                                            offset
                                            (- offset (modulo offset 16))))]
    [else
     (define local->type (first locals->types))
     (define new-offset (- offset (type->size (cdr local->type))))
     (define-values (locals->homes final-offset) (collect-locals->homes (rest locals->types) new-offset))
     (values (dict-set locals->homes (car local->type) (Deref '%rbp new-offset)) final-offset)]))

(define (ah-arg arg locals->homes)
  (match arg
    [(Var x) (dict-ref locals->homes x)]
    [_ arg]))

(define (ah-instr instr locals->homes)
  (match instr
    [(Instr name args)
     (define args/homes (map (λ (a)
                               (ah-arg a locals->homes)) args))
     (Instr name args/homes)]
    [_ instr]))

(define (ah-block block locals->homes)
  (match block
    [(Block info instrs) (Block info (map (λ (i)
                                            (ah-instr i locals->homes)) instrs))]))

(define (assign-homes p)
  (match p
    [(X86Program info blocks)
     (define locals->types (dict-ref info 'locals->types))
     (define-values (locals->homes stack-space) (collect-locals->homes locals->types))
     (define new-info (dict-set info 'stack-space stack-space))
     (define body/assigned-homes (for/list ([(label block) (in-dict blocks)])
                                   (cons label (ah-block block locals->homes))))
     (X86Program new-info body/assigned-homes)]))

(define (patch-instr instr)
  (match instr
    [(Instr name (list arg1
                       arg2))
     #:when (and (Deref? arg1)
                 (Deref? arg2))
     (list (Instr 'movq (list arg1 (Reg 'rax)))
           (Instr name (list (Reg 'rax) arg2)))]
    [_ instr]))

(define (patch-block block)
  (match block
    [(Block info instrs)
     (Block info (flatten (map patch-instr instrs)))]))

(define (patch-instructions p)
  (match p
    [(X86Program info blocks) (X86Program info (for/list ([(label block) (in-dict blocks)])
                                                 (cons label (patch-block block))))]))

(define (generate-prelude)
  (Block '()
         (list (Instr 'pushq (list (Reg 'rbp)))
               (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
               (Instr 'subq (list (Imm 16) (Reg 'rsp)))
               (Jmp 'start))))

(define (generate-conclusion)
  (Block '()
         (list (Instr 'addq (list (Imm 16) (Reg 'rsp)))
               (Instr 'popq (list (Reg 'rbp)))
               (Retq))))

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (define prelude (generate-prelude))
     (define conclusion (generate-conclusion))
     (X86Program info (dict-set* blocks
                                 'main prelude
                                 'conclusion conclusion))]))


(define (print-x86-arg! arg)
  (match arg
    [(Imm val) (printf "$~a" val)]
    [(Reg name) (printf "%~a" name)]
    [(Deref reg offset) (printf "~a(~a)"
                                offset
                                reg)]))

(define (print-x86-instr! instr)
  (match instr
    [(Instr name (list arg)) (printf "~a " name)
                             (print-x86-arg! arg)
                             (printf "\n")]
    [(Instr name (list arg1 arg2)) (printf "~a " name)
                                   (print-x86-arg! arg1)
                                   (printf ", ")
                                   (print-x86-arg! arg2)
                                   (printf "\n")]
    [(Callq label arity) (printf "\n")]
    [(Retq) (printf "retq\n")]
    [(Jmp label) (printf "jmp ~a\n" label)]))

(define (print-x86-block! block)
  (match-define (cons label blk) block)
  (match-define (Block info instrs) blk)
  (printf "~a:\n" label)
  (for-each print-x86-instr! instrs))

(define (print-x86! p)
  (match p
    [(X86Program info blocks)
     (printf ".globl main\n")
     (for-each print-x86-block! blocks)]))

(define passes (list uniquify
                     remove-complex-opera*
                     collect-locals->types
                     explicate-control
                     select-instructions
                     assign-homes
                     patch-instructions
                     prelude-and-conclusion))

(define (compile p)
  (for/fold ([p p])
            ([pass passes])
    (pass p)))

(module+ test
  (with-output-to-file "test.S" #:exists 'truncate
    (λ ()
      (print-x86! (compile example-prog)))))
