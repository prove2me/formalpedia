-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNSq_s3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T17:18:00.321572+00:00
-- url     : https://prove2.me/submissions/56f7a0ab-e37f-4861-9327-e21d21120957

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Theorems.Thm_MazurTransfer_order27_nsq_complete_polynomial_identity
import Definitions.Def_MazurTransfer_Order27NSqPolynomialData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
namespace MazurTransfer.Order27NSqPolynomial
open Polynomial

theorem eval_p_tlN0 (f x : ℚ) :
  (p_tlN0 f).eval x = MazurTorsion.Kubert.tlN0 f x := by
  simp only [p_tlN0, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlN0
  ring

theorem eval_p_tlN1 (f x : ℚ) :
  (p_tlN1 f).eval x = MazurTorsion.Kubert.tlN1 f x := by
  simp only [p_tlN1, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlN1
  ring

theorem eval_p_tlN2 (f x : ℚ) :
  (p_tlN2 f).eval x = MazurTorsion.Kubert.tlN2 f x := by
  simp only [p_tlN2, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlN2
  ring

theorem eval_p_tlN3 (f x : ℚ) :
  (p_tlN3 f).eval x = MazurTorsion.Kubert.tlN3 f x := by
  simp only [p_tlN3, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlN3
  ring

theorem eval_p_tlT0 (f x : ℚ) :
  (p_tlT0 f).eval x = MazurTorsion.Kubert.tlT0 f x := by
  simp only [p_tlT0, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlT0
  ring

theorem eval_p_tlT1 (f x : ℚ) :
  (p_tlT1 f).eval x = MazurTorsion.Kubert.tlT1 f x := by
  simp only [p_tlT1, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlT1
  ring

theorem eval_p_tlT2 (f x : ℚ) :
  (p_tlT2 f).eval x = MazurTorsion.Kubert.tlT2 f x := by
  simp only [p_tlT2, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlT2
  ring

theorem eval_p_tlT3 (f x : ℚ) :
  (p_tlT3 f).eval x = MazurTorsion.Kubert.tlT3 f x := by
  simp only [p_tlT3, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlT3
  ring

theorem eval_p_tlNSqP3c0 (f x : ℚ) :
  (p_tlNSqP3c0 f).eval x = MazurTorsion.Kubert.tlNSqP3c0 f x := by
  simp only [p_tlNSqP3c0, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c0
  ring

theorem eval_p_tlNSqP3c1 (f x : ℚ) :
  (p_tlNSqP3c1 f).eval x = MazurTorsion.Kubert.tlNSqP3c1 f x := by
  simp only [p_tlNSqP3c1, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c1
  ring

theorem eval_p_tlNSqP3c2 (f x : ℚ) :
  (p_tlNSqP3c2 f).eval x = MazurTorsion.Kubert.tlNSqP3c2 f x := by
  simp only [p_tlNSqP3c2, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c2
  ring

theorem eval_p_tlNSqP3c3 (f x : ℚ) :
  (p_tlNSqP3c3 f).eval x = MazurTorsion.Kubert.tlNSqP3c3 f x := by
  simp only [p_tlNSqP3c3, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c3
  ring

theorem eval_p_tlNSqP3c4 (f x : ℚ) :
  (p_tlNSqP3c4 f).eval x = MazurTorsion.Kubert.tlNSqP3c4 f x := by
  simp only [p_tlNSqP3c4, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c4
  ring

theorem eval_p_tlNSqP3c5 (f x : ℚ) :
  (p_tlNSqP3c5 f).eval x = MazurTorsion.Kubert.tlNSqP3c5 f x := by
  simp only [p_tlNSqP3c5, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c5
  ring

theorem eval_p_tlNSqP3c6 (f x : ℚ) :
  (p_tlNSqP3c6 f).eval x = MazurTorsion.Kubert.tlNSqP3c6 f x := by
  simp only [p_tlNSqP3c6, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c6
  ring

theorem eval_p_tlNSqP3c7 (f x : ℚ) :
  (p_tlNSqP3c7 f).eval x = MazurTorsion.Kubert.tlNSqP3c7 f x := by
  simp only [p_tlNSqP3c7, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c7
  ring

theorem eval_p_tlNSqP3c8 (f x : ℚ) :
  (p_tlNSqP3c8 f).eval x = MazurTorsion.Kubert.tlNSqP3c8 f x := by
  simp only [p_tlNSqP3c8, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c8
  ring

theorem eval_p_tlNSqP3c9 (f x : ℚ) :
  (p_tlNSqP3c9 f).eval x = MazurTorsion.Kubert.tlNSqP3c9 f x := by
  simp only [p_tlNSqP3c9, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c9
  ring

theorem eval_p_tlNSqP3c10 (f x : ℚ) :
  (p_tlNSqP3c10 f).eval x = MazurTorsion.Kubert.tlNSqP3c10 f x := by
  simp only [p_tlNSqP3c10, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c10
  ring

theorem eval_p_tlNSqP3c11 (f x : ℚ) :
  (p_tlNSqP3c11 f).eval x = MazurTorsion.Kubert.tlNSqP3c11 f x := by
  simp only [p_tlNSqP3c11, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqP3c11
  ring

theorem eval_p_tlNSqQ3c0 (f x : ℚ) :
  (p_tlNSqQ3c0 f).eval x = MazurTorsion.Kubert.tlNSqQ3c0 f x := by
  simp only [p_tlNSqQ3c0, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqQ3c0
  ring

theorem eval_p_tlNSqQ3c1 (f x : ℚ) :
  (p_tlNSqQ3c1 f).eval x = MazurTorsion.Kubert.tlNSqQ3c1 f x := by
  simp only [p_tlNSqQ3c1, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqQ3c1
  ring

theorem eval_p_tlNSqQ3c2 (f x : ℚ) :
  (p_tlNSqQ3c2 f).eval x = MazurTorsion.Kubert.tlNSqQ3c2 f x := by
  simp only [p_tlNSqQ3c2, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqQ3c2
  ring

theorem eval_p_tlNSqQ3c3 (f x : ℚ) :
  (p_tlNSqQ3c3 f).eval x = MazurTorsion.Kubert.tlNSqQ3c3 f x := by
  simp only [p_tlNSqQ3c3, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqQ3c3
  ring

theorem eval_p_tlNSqQ3c4 (f x : ℚ) :
  (p_tlNSqQ3c4 f).eval x = MazurTorsion.Kubert.tlNSqQ3c4 f x := by
  simp only [p_tlNSqQ3c4, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqQ3c4
  ring

theorem eval_p_tlNSqQ3c5 (f x : ℚ) :
  (p_tlNSqQ3c5 f).eval x = MazurTorsion.Kubert.tlNSqQ3c5 f x := by
  simp only [p_tlNSqQ3c5, Polynomial.eval_add, Polynomial.eval_monomial]
  unfold MazurTorsion.Kubert.tlNSqQ3c5
  ring

end MazurTransfer.Order27NSqPolynomial
#print axioms MazurTransfer.Order27NSqPolynomial.eval_p_tlN3

open Polynomial MazurTorsion.Kubert MazurTransfer.Order27NSqPolynomial

theorem solution :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlN3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP3c0 f ξ + tlNSqP3c1 f ξ) + (tlNSqP3c2 f ξ + tlNSqP3c3 f ξ)) + ((tlNSqP3c4 f
        ξ + tlNSqP3c5 f ξ) + (tlNSqP3c6 f ξ + tlNSqP3c7 f ξ))) + ((tlNSqP3c8 f ξ +
        tlNSqP3c9 f ξ) + (tlNSqP3c10 f ξ + tlNSqP3c11 f ξ))) := by
 intro f ξ hT
 have h := congrArg (fun p : ℚ[X] => p.eval ξ)
   (MazurTransfer.order27_nsq_complete_polynomial_identity f)
 simp only [leftSide, rightSide, Polynomial.eval_add, Polynomial.eval_mul, eval_p_tlN0, eval_p_tlN1, eval_p_tlN2, eval_p_tlN3, eval_p_tlT0, eval_p_tlT1, eval_p_tlT2, eval_p_tlT3, eval_p_tlNSqP3c0, eval_p_tlNSqP3c1, eval_p_tlNSqP3c2, eval_p_tlNSqP3c3, eval_p_tlNSqP3c4, eval_p_tlNSqP3c5, eval_p_tlNSqP3c6, eval_p_tlNSqP3c7, eval_p_tlNSqP3c8, eval_p_tlNSqP3c9, eval_p_tlNSqP3c10, eval_p_tlNSqP3c11, eval_p_tlNSqQ3c0, eval_p_tlNSqQ3c1, eval_p_tlNSqQ3c2, eval_p_tlNSqQ3c3, eval_p_tlNSqQ3c4, eval_p_tlNSqQ3c5] at h
 have hT' : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0 := by
  simpa only [add_assoc] using hT
 rw [hT', mul_zero, add_zero] at h
 simpa only [add_assoc] using h

#print axioms solution
