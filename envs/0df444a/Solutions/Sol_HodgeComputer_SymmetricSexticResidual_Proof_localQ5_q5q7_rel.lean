-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_rel
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:21:17.9828+00:00
-- url     : https://prove2.me/submissions/f96df0c7-0dea-426e-a858-c4d9c54f1d95

import Definitions.Def_HodgeComputerSSR_Q5Weights
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.Q5WeightsData PolynomialEncoding.KroneckerCheck PolynomialEncoding.PolyOps

lemma q5Dot_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 : α}
    {q0' q1' q2' q3' q4' q5' a0' a1' a2' a3' a4' a5' : β}
    (hq0 : R q0 q0') (hq1 : R q1 q1') (hq2 : R q2 q2') (hq3 : R q3 q3') (hq4 : R q4 q4') (hq5 : R q5 q5')
    (ha0 : R a0 a0') (ha1 : R a1 a1') (ha2 : R a2 a2') (ha3 : R a3 a3') (ha4 : R a4 a4') (ha5 : R a5 a5') :
    R (q5Dot o1 q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5) (q5Dot o2 q0' q1' q2' q3' q4' q5' a0' a1' a2' a3' a4' a5') :=
  hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_mul hq0 ha0) (hR.rel_mul hq1 ha1))
    (hR.rel_add (hR.rel_mul hq2 ha2) (hR.rel_mul hq3 ha3)))
    (hR.rel_add (hR.rel_mul hq4 ha4) (hR.rel_mul hq5 ha5))


lemma q7Dot_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 : α}
    {q0' q1' q2' q3' q4' q5' q6' q7' a0' a1' a2' a3' a4' a5' a6' a7' : β}
    (hq0 : R q0 q0') (hq1 : R q1 q1') (hq2 : R q2 q2') (hq3 : R q3 q3')
    (hq4 : R q4 q4') (hq5 : R q5 q5') (hq6 : R q6 q6') (hq7 : R q7 q7')
    (ha0 : R a0 a0') (ha1 : R a1 a1') (ha2 : R a2 a2') (ha3 : R a3 a3')
    (ha4 : R a4 a4') (ha5 : R a5 a5') (ha6 : R a6 a6') (ha7 : R a7 a7') :
    R (q7Dot o1 q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7)
      (q7Dot o2 q0' q1' q2' q3' q4' q5' q6' q7' a0' a1' a2' a3' a4' a5' a6' a7') :=
  hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_mul hq0 ha0) (hR.rel_mul hq1 ha1))
    (hR.rel_add (hR.rel_mul hq2 ha2) (hR.rel_mul hq3 ha3)))
    (hR.rel_add (hR.rel_add (hR.rel_mul hq4 ha4) (hR.rel_mul hq5 ha5))
      (hR.rel_add (hR.rel_mul hq6 ha6) (hR.rel_mul hq7 ha7)))


lemma q5q7RecList_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β} (hS : R S1 S2) (hQ : R Q1 Q2) :
    List.Forall₂ R (q5q7RecList o1 S1 Q1) (q5q7RecList o2 S2 Q2) := by
  unfold q5q7RecList
  refine letB_rel (powList_rel hR hS 30 (hR.rel_ofInt 1)) fun hpS => ?_
  refine letB_rel (powList_rel hR hQ 37 (hR.rel_ofInt 1)) fun hpQ => ?_
  refine letB_rel (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-5)) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hf2 => ?_
  refine letB_rel (hR.rel_add (hR.rel_neg hS) (hR.rel_mul (hR.rel_ofInt 3) hQ)) fun hf3 => ?_
  refine letB_rel (hR.rel_add (hR.rel_add (hR.rel_ofInt (-45)) (hR.rel_mul (hR.rel_ofInt (-77)) hS)) (hR.rel_mul (hR.rel_ofInt 210) hQ)) fun hf4 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ fac_5) fun hf5 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ fac_6) fun hf6 => ?_
  refine letB_rel (hR.rel_mul hf2 hf2) fun hf2_2 => ?_
  refine letB_rel (hR.rel_mul hf2_2 hf2_2) fun hf2_4 => ?_
  refine letB_rel (hR.rel_mul hf2_4 hf2_2) fun hf2_6 => ?_
  refine letB_rel (hR.rel_mul hf2_6 hf2) fun hf2_7 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul hf3 hf3) hf3) fun hf3_3 => ?_
  refine letB_rel (hR.rel_mul hf3_3 hf3_3) fun hf3_6 => ?_
  refine letB_rel (hR.rel_mul hf3_6 hf3_3) fun hf3_9 => ?_
  refine letB_rel (hR.rel_mul hf3_9 hf3_3) fun hf3_12 => ?_
  refine letB_rel (hR.rel_mul hf3_12 hf3) fun hf3_13 => ?_
  refine letB_rel (hR.rel_mul hf4 hf4) fun hf4_2 => ?_
  refine letB_rel (hR.rel_mul hf3_13 hf4_2) fun hd0 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_2) hf3_13) hf4_2) fun hd1 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_4) hf3_13) hf4_2) fun hd2 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_6) hf3_13) hf4_2) fun hd3 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_13) hf4_2) fun hd4 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_12) hf4_2) fun hd8 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_9) hf4_2) fun hd9 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_6) hf4_2) fun hd10 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_3) hf4) fun hd11 => ?_
  refine letB_rel (hR.rel_mul hS hf2_7) fun hd12 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd0 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW0 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd1 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW1 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd2 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW2 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd3 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW3 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW4 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW5 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW6 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW7 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd8 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW8 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd9 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW9 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd10 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW10 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd11 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW11 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd12 (evalExpr2_rel hR hS hQ hpS hpQ _))) fun hW12 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c0) fun hq50 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c1) fun hq51 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c2) fun hq52 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c3) fun hq53 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c4) fun hq54 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q5_c5) fun hq55 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c0) fun hq70 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c1) fun hq71 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c2) fun hq72 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c3) fun hq73 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c4) fun hq74 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c5) fun hq75 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c6) fun hq76 => ?_
  refine letB_rel (evalExpr2_rel hR hS hQ hpS hpQ Q7_c7) fun hq77 => ?_
  refine letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul hQ hS) hf2_7) hf3_9) hf4)
    (hR.rel_pow 4 hf5)) hf6) fun hdlc5 => ?_
  exact List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW0 hW1 hW2 hW3 hW4 hW5)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW1 hW2 hW3 hW4 hW5 hW6)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW2 hW3 hW4 hW5 hW6 hW7)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW3 hW4 hW5 hW6 hW7 hW8)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW4 hW5 hW6 hW7 hW8 hW9)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW5 hW6 hW7 hW8 hW9 hW10)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW6 hW7 hW8 hW9 hW10 hW11)
    (List.Forall₂.cons (q5Dot_rel hR hq50 hq51 hq52 hq53 hq54 hq55 hW7 hW8 hW9 hW10 hW11 hW12)
    (List.Forall₂.cons (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW0 hW1 hW2 hW3 hW4 hW5 hW6 hW7)
    (List.Forall₂.cons (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW1 hW2 hW3 hW4 hW5 hW6 hW7 hW8)
    (List.Forall₂.cons (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW2 hW3 hW4 hW5 hW6 hW7 hW8 hW9)
    (List.Forall₂.cons (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW3 hW4 hW5 hW6 hW7 hW8 hW9 hW10)
    (List.Forall₂.cons (hR.rel_sub (hR.rel_mul (hR.rel_ofInt _)
        (q7Dot_rel hR hq70 hq71 hq72 hq73 hq74 hq75 hq76 hq77 hW4 hW5 hW6 hW7 hW8 hW9 hW10 hW11))
      (hR.rel_mul (hR.rel_ofInt _) hdlc5)) List.Forall₂.nil))))))))))))


end SymmetricSexticResidual.LocalResidueQ5

theorem solution :
    ∀ {α β : Type} {o1 : PolynomialEncoding.KroneckerCheck.PolyOps α} {o2 : PolynomialEncoding.KroneckerCheck.PolyOps β}
      {R : α → β → Prop},
      PolynomialEncoding.KroneckerCheck.PolyOpsRel o1 o2 R →
      ∀ {S1 Q1 : α} {S2 Q2 : β}, R S1 S2 → R Q1 Q2 →
      List.Forall₂ R
        (SymmetricSexticResidual.LocalResidueQ5.q5q7RecList o1 S1 Q1)
        (SymmetricSexticResidual.LocalResidueQ5.q5q7RecList o2 S2 Q2) :=
  SymmetricSexticResidual.LocalResidueQ5.q5q7RecList_rel
