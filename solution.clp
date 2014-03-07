(deffunction set-fact (?f ?v)
   (assert (is-fact ?f ?v)))

(deffunction answer (?ans)
   (printout t crlf "You should better ")
   (printout t ?ans ".")
   (printout t crlf crlf))

(deffunction ask-question (?question $?allowed-values)
   (printout t ?question)
   (printout t ?allowed-values)
   (bind ?answer (read))
   (if (lexemep ?answer) 
       then (bind ?answer (lowcase ?answer)))
   (while (not (member ?answer ?allowed-values)) do
      (printout t ?question)
      (bind ?answer (read))
      (if (lexemep ?answer) 
          then (bind ?answer (lowcase ?answer))))
   ?answer)

;;;(defrule uncertainity-wins
;;;   ?f <- (certainity 0)
;;;   (not (is-fact $?))
;;;  =>
;;;   (retract ?f)
;;;   (answer "fold"))

(deffunction ask ($?what)
   (printout t $?what)
   (bind ?response (ask-question "" yes no y n))
   (if (or (eq ?response yes) (eq ?response y))
       then TRUE 
       else FALSE))

(defrule uncertainity-wins2
   (not (game-ended))
   ?f <- (certainity ?x)
   ?c <- (situation $?)
   (test (> 2 ?x))
  =>
   (retract ?f)
   (retract ?c)
   (assert (game-ended))
   (printout t "Your estimation is not to be trusted" crlf)
   (if (ask "Do you have much to lose?")
    then
   	(answer "fold")
    else 
	  (answer "pass")))

(defrule assess-situation
   (declare (salience -2))
   (not (game-ended))
   ?f <- (situation ?x)
   (not (is-fact $?))
   (not (question-to-ask $?))
   (not (question $?))
   (certainity ?y)
   (test (< 1 ?y))
   =>
   (assert (game-ended))
   (retract ?f)
   (if (> 1 ?x)
      then (answer "fold"))
   (if (and (< 0 ?x) (> 3 ?x))
      then (answer "pass"))
   (if (< 2 ?x)
      then (answer "raise")))

(deffunction add-question (?question ?fact $?allowed-values)
   (assert (question-to-ask ?question ?fact ?allowed-values)))

(defrule ask-question-rule
   (declare (salience -1))
   (not (game-ended))
   ?f <- (question-to-ask ?question ?fact $?allowed-values)
   =>
   (bind ?ans (ask-question ?question ?allowed-values))
   (set-fact ?fact ?ans)
   (retract ?f)
   )

(defrule add-numbered-question
   (not (game-ended))
   ?f <- (questions)
   =>
   (add-question "How long do you play poker?" certainity long medium short unknown)
   (add-question "How good are you compared to your oponnents?" oponnents good bad medium unknown)
   (add-question "Are your cards rather good or not?" cards good bad medium unknown)
   (add-question "How good are your cards compared to those on table?" table good bad unknown)
   (retract ?f)
   )

(deffacts beginning 
   (certainity 3)
   (situation 2)
   (questions)
	)

(deffunction make-sure (?what ?how)
    ask "Are you sure that " ?what " are " ?how)

(defrule type-reaction-good
    (declare (salience -1))
   (not (game-ended))
    ?f <- (is-fact ?w good)
    (certainity ?v)
    ?c <- (situation ?s)
    =>
    (retract ?f)
    (assert (hist-fact ?w good))
    (retract ?c)
    (if (or (>= ?v  3) (make-sure ?w good))
       then (assert (situation (+ ?s 1)))
       else (set-fact ?w unknown)))

(defrule type-reaction-medium
    (declare (salience -1))
   (not (game-ended))
    ?c <- (is-fact ?w medium)
    =>
    (assert (hist-fact ?w medium))
   (retract ?c))

(defrule type-reaction-bad
    (declare (salience -1))
   (not (game-ended))
    ?c <- (is-fact ?w bad)
    ?f <- (situation ?s)
    =>
    (retract ?f)
    (retract ?c)   
    (assert (hist-fact ?w bad))
    (assert (situation (- ?s 1))))
   

(defrule type-reaction-unknown
    (declare (salience -1))
   (not (game-ended))
    ?c <- (is-fact ?x unknown)
    ?f <- (certainity ?v)
    =>
    (retract ?f)
    (retract ?c)
    (assert (hist-fact ?x unknown))
    (assert (certainity (- ?v 1))))

(defrule card-type-reaction-bad
   (not (game-ended))
    ?c <- (is-fact cards bad)
    ?f <- (situation ?s)
    =>
    (retract ?f)
    (retract ?c)
    (assert (hist-fact cards bad))
    (if (make-sure cards bad)
        then   
        (assert (situation (- ?s 2)))
        else 
        (assert (situation (- ?s 1))))
    )
    
(defrule oponnents-type-reaction-medium
   (not (game-ended))
    ?c <- (is-fact oponnents medium)
    =>
    (retract ?c)
    (assert (hist-fact oponnents medium))
    (add-question "How much longer do they play poker then you?" exp ages little))

(defrule exp-type-reaction-ages
   (not (game-ended))
    ?c  <- (is-fact exp ages)
    ?ce <- (certainity ?v)
    =>
    (retract ?c)
    (retract ?ce)   
    (assert (hist-fact exp ages))
    (assert (certainity (- ?v 2)))
    (assert (is-fact situation bad)))    

(defrule exp-type-reaction-little
   (not (game-ended))
    ?c  <- (is-fact exp little)
    ?ce <- (certainity ?v)
    =>
    (retract ?c)
    (assert (hist-fact exp little))
    (retract ?ce)   
    (assert (certainity (+ ?v 1)))
    (assert (is-fact situation medium)))    

(defrule hist-good-cards-good-oponnents
   (not (game-ended))
    (not (hist-fact great-situation))
    (hist-fact cards good)
    (hist-fact oponnents good|medium)
    =>
    (assert (hist-fact great-situation))
    (assert (is-fact situation good))
    (printout t "You are in really good situation." crlf))

(defrule hist-good-cards-bad-oponnents
   (not (game-ended))
    (not (hist-fact oponnents-bluffing))
    (hist-fact cards good)
    (hist-fact oponnents bad|medium)
    =>
    (assert (hist-fact oponnents-bluffing))
    (if (ask "Is it possible your oponnents are bluffing?")
	then 
    	   (assert (is-fact situation medium))
    	else 
	   (assert (is-fact situation bad))))

(defrule hist-bad-cards-good-oponnents
   (not (game-ended))
    (not (hist-fact should-bluff))
    (hist-fact cards bad|medium)
    (hist-fact oponnents good|medium)
    =>
    (assert (hist-fact should-bluff))
    (if (ask "Do you feel confident bluffing?")
	then 
    	   (assert (is-fact situation good))
    	else 
	   (assert (is-fact situation medium))))

(defrule certainity-type-reaction-long
   (not (game-ended))
    ?c  <- (is-fact certainity long)
    ?ce <- (certainity ?v)
    =>
    (retract ?c)
    (retract ?ce)   
    (assert (hist-fact certainity long))
    (assert (certainity (+ ?v 2))))

(defrule certainity-type-reaction-medium
   (not (game-ended))
    ?c  <- (is-fact certainity medium)
    =>
    (retract ?c)
    (assert (hist-fact certainity medium)))


(defrule certainity-type-reaction-short
   (not (game-ended))
    ?c  <- (is-fact certainity short)
    ?ce <- (certainity ?v)
    =>
    (retract ?c)
    (retract ?ce)   
    (assert (hist-fact certainity short))
    (assert (certainity (- ?v 1))))


(defrule certainity-type-reaction-unknown
   (not (game-ended))
    ?c  <- (is-fact certainity unknown)
    ?ce <- (certainity ?v)
    =>
    (retract ?c)
    (retract ?ce)   
    (assert (hist-fact certainity unknown))
    (assert (certainity (- ?v 2))))
