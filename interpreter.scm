;INITIAL ENVIRONMENT

(define global-env   (list  (list	
(list	'+	(list'primitive +))
(list	'-	(list'primitive -))
(list	'*	(list'primitive *))
(list	'/	(list'primitive /))
(list	'not	(list'primitive not))
(list	'>	(list'primitive >))
(list	'list	(list'primitive list))
(list	'cons	(list'primitive cons))
(list	'=	(list'primitive =))
(list	'car	(list'primitive car))
(list	'<	(list'primitive <))
(list	'cdr	(list'primitive cdr))
(list	'append	(list'primitive append))
(list	'length (list'primitive length))
(list   'true	true)
(list   'false  false))))
(define keyword (list
(list #\+ '+)
(list #\- '-)
(list #\* '*)
(list #\/ '/)
(list #\> '>)
(list #\= '=)
(list #\< '<)
(list '#t 'true)
(list '#f '#f)
))
(define (keyword? key l) (if (null? l) key (if( eq? (caar l) key)  (cadar l) (keyword? key (cdr l))) ) )

;PARSER
(define token-list '())
(define (appendu l1 l2) (append l1 (list l2)))
(define (parser) (set! token-list (tokenizer)) (read-from ))

(define (read-from )	(if(= (length token-list) 0) (error "unexpected EOF while reading")
					(let ((token (car token-list)))  (begin (set! token-list (cdr token-list))
					(cond((eq? left-parenthesis-token token)
(let ((L'())) (begin (do () ((eq? (car token-list) right-parenthesis-token)) (set! L (appendu L (read-from)))) (set! token-list (cdr token-list)))L))
										((eq? right-parenthesis-token token) (error "Unexpected )"))
										(else (keyword? token keyword)))))))

  
(define (read-token)
   (let ((char-read (read-char)))
      (cond ((char-space? char-read)
             (read-token))
            ((char-newline? char-read) char-newline)
            ((eq? char-read #\( )
             left-parenthesis-token)
            ((eq? char-read #\) )
             right-parenthesis-token)
            ((char-alphabetic? char-read)
             (readid char-read))
            ((char-numeric? char-read)
             (readnum char-read))
             ((char-operator? char-read) char-read)
             ((eq? char-read #\!) '!)
            (else
             (error "illegal lexical syntax")))))

(define char-space #\space)
(define (char-space? char) (eq? char char-space))             
(define char-newline #\newline)
(define (char-newline? char) (eq? char char-newline))             



(define (readnum chr)
  (define (readnum-iter numlist)
     (let ((next-char (peek-char)))
       (if (char-numeric? next-char)
          (readnum-iter (cons (read-char) numlist))
 	          (reverse numlist))))
  (string->number (list->string (readnum-iter (list chr)))))

(define (readid chr)
   (define (readid-iter idlist)
    (let ((next-char (peek-char)))
            (if (or (char-alphabetic? next-char)
              (char-numeric? next-char))
	          (readid-iter (cons (read-char) idlist))
		          (reverse idlist))))
      (string->symbol(list->string (readid-iter (list chr)))))




(define left-parenthesis-token #\( )
(define right-parenthesis-token #\) ) 
(define (reverse l)(cond((null? (cdr l)) (list(car l)))(else (append (reverse (cdr l)) (list(car l))))))
(define (tokenizer) (let((token (list (read-token)))) (if(char-newline? (car token)) (list) (append token  (tokenizer)))))
(define char-operator (list #\+ #\- #\* #\/ #\< #\> #\=))
(define (char-operator? token) (define (check l t) (cond((null? l) #f)
							((eq? (car l) t) #t)
							(else (check (cdr l) t))))
								(check char-operator token))


;ENVIRONMENT OPERATIONS

(define (set var val env)
(define	(set-var var val env )
	(define (scan innerenvs) (cond((null? innerenvs) '())
				((eq? (caar innerenvs)  var) (append (list(list var val)) (scan (cdr innerenvs))))
				(else (append (list(car innerenvs)) (scan (cdr innerenvs))))	))
				(if (null? env) (if (eq? (list (find var global-env)) '()) (error "Unbound variablE:" var)	'()) 
		                           (let((innerenv (car env)))(append (list(scan innerenv))(set-var var val (cdr env))))))
		         (set! global-env (set-var var val env) ) "value-set")



(define (find var env )
	(define (scan var inner-env)
		(cond   ((null? inner-env) '())
			((eq? (caar inner-env) var) (cdar inner-env))
			(else (scan var (cdr inner-env)))))
  (if(null? env) (error "Unbound variablE:" var) 
  (let ((inner (car env))) (if(eq? (scan var inner) '()) (find var (cdr env)) (car(scan var inner))))))




(define (extend var val  base) (append (list(zip var val)) base))


(define (zip var val) (if(null? (cdr var))    (list(list (car var) (car val)))
			(append (list(list (car var) (car val))) (zip (cdr var) (cdr val)))))



(define (def var val env) 
(define (def-var var val env)
(define (scan innerenv len) (cond((null? innerenv) (if (<= len (length (car env)))  (list(list var val)) '()))
				((eq? (caar innerenv) var) (append '() (scan (cdr innerenv) (- len 1))))
				(else (append (list(car innerenv)) (scan (cdr innerenv) len)))))
				(append (list (scan (car env) (length (car env)))) (cdr env)))
(set! global-env (def-var var val env)) "var-defined" )


;EVALUATOR


(define (evalte expr env)
  (cond ((or (number? expr) (string? expr)) expr)
 	((symbol? expr) (find expr env))
        ((quote? expr) (cadr expr))
        ((if? expr) (evalte (if(evalte (cadr expr) env) (evalte (caddr expr) env)  (evalte (cadddr expr) env) )env))
        ((set!? expr) (set (caddr expr) (evalte (cadddr expr) env) env))
        ((define? expr) (def (cadr expr) (evalte (caddr expr) env) env))
        ((begin? expr) (evaltebegin (cdr expr)))
	((lambda? expr) (list 'procedure (cadr expr) (caddr expr)))
	((eq? (car expr) 'exit) (exit))
	(else (let ((exps (map (lambda (x) (evalte x env)) expr))) (if(eq?(car-list?  (car exps) ) 'procedure)   
					 (evalte (caddar exps) (extend (cadar exps) (cdr exps) global-env))
										(apply (cadar exps) (cdr exps))))) 
        ))


(define (car-list? expr) (car expr))
(define (quote? expr)(eq? (car-list? expr) 'quote))
(define (define? expr)(eq? (car-list? expr) 'define))
(define (if? expr)(eq? (car-list? expr) 'if))

(define (set!? expr)(eq? (car-list? expr) 'set))

(define (begin? expr)(eq? (car-list? expr) 'begin))
(define (evaltebegin expr)
(last (map (lambda (x) (evalte x global-env)) expr)))
(define (last l) (if(null? (cdr l))   (car l)   (last (cdr l)) ))


(define (lambda? expr)(eq? (car-list? expr) 'lambda))  


;INTERPRETER

(define (prompt) (newline)(display "=>> ") (evalte (parser) global-env) )
(define (interpreter) (begin (write (prompt)) (interpreter)))
(interpreter)
