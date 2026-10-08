-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T17:21:25.09399+00:00
-- url     : https://prove2.me/submissions/55244d21-0067-4538-a8d6-7590f38057c8

import Theorems.Thm_MazurTransfer_order27_ttwo2_complete_polynomial_identity
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27TTwo2PolynomialData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
namespace MazurTransfer.Order27TTwo2Polynomial
open Polynomial

theorem eval_p_tlNSqP0c6 (f x : ℚ) :
 (p_tlNSqP0c6 f).eval x = MazurTorsion.Kubert.tlNSqP0c6 f x := by
 simp only [p_tlNSqP0c6, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNSqP0c6
 ring

theorem eval_p_tlNSqP0c7 (f x : ℚ) :
 (p_tlNSqP0c7 f).eval x = MazurTorsion.Kubert.tlNSqP0c7 f x := by
 simp only [p_tlNSqP0c7, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNSqP0c7
 ring

theorem eval_p_tlNSqP0c8 (f x : ℚ) :
 (p_tlNSqP0c8 f).eval x = MazurTorsion.Kubert.tlNSqP0c8 f x := by
 simp only [p_tlNSqP0c8, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNSqP0c8
 ring

theorem eval_p_tlNSqP1c0 (f x : ℚ) :
 (p_tlNSqP1c0 f).eval x = MazurTorsion.Kubert.tlNSqP1c0 f x := by
 simp only [p_tlNSqP1c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNSqP1c0
 ring

theorem eval_p_tlD0 (f x : ℚ) :
 (p_tlD0 f).eval x = MazurTorsion.Kubert.tlD0 f x := by
 simp only [p_tlD0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlD0
 ring

theorem eval_p_tlD1 (f x : ℚ) :
 (p_tlD1 f).eval x = MazurTorsion.Kubert.tlD1 f x := by
 simp only [p_tlD1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlD1
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

theorem eval_p_tlTTwoP2c0 (f x : ℚ) :
 (p_tlTTwoP2c0 f).eval x = MazurTorsion.Kubert.tlTTwoP2c0 f x := by
 simp only [p_tlTTwoP2c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c0
 ring

theorem eval_p_tlTTwoP2c1 (f x : ℚ) :
 (p_tlTTwoP2c1 f).eval x = MazurTorsion.Kubert.tlTTwoP2c1 f x := by
 simp only [p_tlTTwoP2c1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c1
 ring

theorem eval_p_tlTTwoP2c2 (f x : ℚ) :
 (p_tlTTwoP2c2 f).eval x = MazurTorsion.Kubert.tlTTwoP2c2 f x := by
 simp only [p_tlTTwoP2c2, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c2
 ring

theorem eval_p_tlTTwoP2c3 (f x : ℚ) :
 (p_tlTTwoP2c3 f).eval x = MazurTorsion.Kubert.tlTTwoP2c3 f x := by
 simp only [p_tlTTwoP2c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c3
 ring

theorem eval_p_tlTTwoP2c4 (f x : ℚ) :
 (p_tlTTwoP2c4 f).eval x = MazurTorsion.Kubert.tlTTwoP2c4 f x := by
 simp only [p_tlTTwoP2c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c4
 ring

theorem eval_p_tlTTwoP2c5 (f x : ℚ) :
 (p_tlTTwoP2c5 f).eval x = MazurTorsion.Kubert.tlTTwoP2c5 f x := by
 simp only [p_tlTTwoP2c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c5
 ring

theorem eval_p_tlTTwoP2c6 (f x : ℚ) :
 (p_tlTTwoP2c6 f).eval x = MazurTorsion.Kubert.tlTTwoP2c6 f x := by
 simp only [p_tlTTwoP2c6, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c6
 ring

theorem eval_p_tlTTwoP2c7 (f x : ℚ) :
 (p_tlTTwoP2c7 f).eval x = MazurTorsion.Kubert.tlTTwoP2c7 f x := by
 simp only [p_tlTTwoP2c7, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c7
 ring

theorem eval_p_tlTTwoP2c8 (f x : ℚ) :
 (p_tlTTwoP2c8 f).eval x = MazurTorsion.Kubert.tlTTwoP2c8 f x := by
 simp only [p_tlTTwoP2c8, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c8
 ring

theorem eval_p_tlTTwoP2c9 (f x : ℚ) :
 (p_tlTTwoP2c9 f).eval x = MazurTorsion.Kubert.tlTTwoP2c9 f x := by
 simp only [p_tlTTwoP2c9, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c9
 ring

theorem eval_p_tlTTwoP2c10 (f x : ℚ) :
 (p_tlTTwoP2c10 f).eval x = MazurTorsion.Kubert.tlTTwoP2c10 f x := by
 simp only [p_tlTTwoP2c10, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c10
 ring

theorem eval_p_tlTTwoP2c11 (f x : ℚ) :
 (p_tlTTwoP2c11 f).eval x = MazurTorsion.Kubert.tlTTwoP2c11 f x := by
 simp only [p_tlTTwoP2c11, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c11
 ring

theorem eval_p_tlTTwoP2c12 (f x : ℚ) :
 (p_tlTTwoP2c12 f).eval x = MazurTorsion.Kubert.tlTTwoP2c12 f x := by
 simp only [p_tlTTwoP2c12, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c12
 ring

theorem eval_p_tlTTwoP2c13 (f x : ℚ) :
 (p_tlTTwoP2c13 f).eval x = MazurTorsion.Kubert.tlTTwoP2c13 f x := by
 simp only [p_tlTTwoP2c13, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c13
 ring

theorem eval_p_tlTTwoP2c14 (f x : ℚ) :
 (p_tlTTwoP2c14 f).eval x = MazurTorsion.Kubert.tlTTwoP2c14 f x := by
 simp only [p_tlTTwoP2c14, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c14
 ring

theorem eval_p_tlTTwoP2c15 (f x : ℚ) :
 (p_tlTTwoP2c15 f).eval x = MazurTorsion.Kubert.tlTTwoP2c15 f x := by
 simp only [p_tlTTwoP2c15, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP2c15
 ring

theorem eval_p_tlTTwoQ2c0 (f x : ℚ) :
 (p_tlTTwoQ2c0 f).eval x = MazurTorsion.Kubert.tlTTwoQ2c0 f x := by
 simp only [p_tlTTwoQ2c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ2c0
 ring

theorem eval_p_tlTTwoQ2c1 (f x : ℚ) :
 (p_tlTTwoQ2c1 f).eval x = MazurTorsion.Kubert.tlTTwoQ2c1 f x := by
 simp only [p_tlTTwoQ2c1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ2c1
 ring

theorem eval_p_tlTTwoQ2c2 (f x : ℚ) :
 (p_tlTTwoQ2c2 f).eval x = MazurTorsion.Kubert.tlTTwoQ2c2 f x := by
 simp only [p_tlTTwoQ2c2, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ2c2
 ring

theorem eval_p_tlTTwoQ2c3 (f x : ℚ) :
 (p_tlTTwoQ2c3 f).eval x = MazurTorsion.Kubert.tlTTwoQ2c3 f x := by
 simp only [p_tlTTwoQ2c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ2c3
 ring

theorem eval_p_tlTTwoQ2c4 (f x : ℚ) :
 (p_tlTTwoQ2c4 f).eval x = MazurTorsion.Kubert.tlTTwoQ2c4 f x := by
 simp only [p_tlTTwoQ2c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ2c4
 ring

theorem eval_p_tlTTwoQ2c5 (f x : ℚ) :
 (p_tlTTwoQ2c5 f).eval x = MazurTorsion.Kubert.tlTTwoQ2c5 f x := by
 simp only [p_tlTTwoQ2c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ2c5
 ring

theorem eval_p_tlTTwoQ2c6 (f x : ℚ) :
 (p_tlTTwoQ2c6 f).eval x = MazurTorsion.Kubert.tlTTwoQ2c6 f x := by
 simp only [p_tlTTwoQ2c6, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ2c6
 ring

end MazurTransfer.Order27TTwo2Polynomial

#print axioms MazurTransfer.Order27TTwo2Polynomial.eval_p_tlNSqP0c6

open Polynomial MazurTorsion.Kubert MazurTransfer.Order27TTwo2Polynomial

theorem solution :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP0c6 f ξ + tlNSqP0c7 f ξ + tlNSqP0c8 f ξ + tlNSqP1c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ) + (tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ)) +
        ((tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ) + (tlTTwoP2c6 f ξ + tlTTwoP2c7 f ξ))) +
        (((tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ) + (tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ)) +
        ((tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ) + (tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ)))) := by
 intro f ξ hT
 have h := congrArg (fun p : ℚ[X] => p.eval ξ) (MazurTransfer.order27_ttwo2_complete_polynomial_identity f)
 simp only [leftSide, rightSide, Polynomial.eval_add, Polynomial.eval_mul, eval_p_tlNSqP0c6, eval_p_tlNSqP0c7, eval_p_tlNSqP0c8, eval_p_tlNSqP1c0, eval_p_tlD0, eval_p_tlD1, eval_p_tlT0, eval_p_tlT1, eval_p_tlT2, eval_p_tlT3, eval_p_tlTTwoP2c0, eval_p_tlTTwoP2c1, eval_p_tlTTwoP2c2, eval_p_tlTTwoP2c3, eval_p_tlTTwoP2c4, eval_p_tlTTwoP2c5, eval_p_tlTTwoP2c6, eval_p_tlTTwoP2c7, eval_p_tlTTwoP2c8, eval_p_tlTTwoP2c9, eval_p_tlTTwoP2c10, eval_p_tlTTwoP2c11, eval_p_tlTTwoP2c12, eval_p_tlTTwoP2c13, eval_p_tlTTwoP2c14, eval_p_tlTTwoP2c15, eval_p_tlTTwoQ2c0, eval_p_tlTTwoQ2c1, eval_p_tlTTwoQ2c2, eval_p_tlTTwoQ2c3, eval_p_tlTTwoQ2c4, eval_p_tlTTwoQ2c5, eval_p_tlTTwoQ2c6] at h
 rw [hT, mul_zero, add_zero] at h
 simpa only [add_assoc] using h

#print axioms solution
