-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlTTwo_s5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T17:20:41.923071+00:00
-- url     : https://prove2.me/submissions/8e076814-196e-404a-a9c2-00019c45482e

import Theorems.Thm_MazurTransfer_order27_ttwo5_complete_polynomial_identity
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27TTwo5PolynomialData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
namespace MazurTransfer.Order27TTwo5Polynomial
open Polynomial

theorem eval_p_tlNSqP1c7 (f x : ℚ) :
 (p_tlNSqP1c7 f).eval x = MazurTorsion.Kubert.tlNSqP1c7 f x := by
 simp only [p_tlNSqP1c7, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNSqP1c7
 ring

theorem eval_p_tlNSqP1c8 (f x : ℚ) :
 (p_tlNSqP1c8 f).eval x = MazurTorsion.Kubert.tlNSqP1c8 f x := by
 simp only [p_tlNSqP1c8, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNSqP1c8
 ring

theorem eval_p_tlNSqP1c9 (f x : ℚ) :
 (p_tlNSqP1c9 f).eval x = MazurTorsion.Kubert.tlNSqP1c9 f x := by
 simp only [p_tlNSqP1c9, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNSqP1c9
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

theorem eval_p_tlTTwoP5c0 (f x : ℚ) :
 (p_tlTTwoP5c0 f).eval x = MazurTorsion.Kubert.tlTTwoP5c0 f x := by
 simp only [p_tlTTwoP5c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c0
 ring

theorem eval_p_tlTTwoP5c1 (f x : ℚ) :
 (p_tlTTwoP5c1 f).eval x = MazurTorsion.Kubert.tlTTwoP5c1 f x := by
 simp only [p_tlTTwoP5c1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c1
 ring

theorem eval_p_tlTTwoP5c2 (f x : ℚ) :
 (p_tlTTwoP5c2 f).eval x = MazurTorsion.Kubert.tlTTwoP5c2 f x := by
 simp only [p_tlTTwoP5c2, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c2
 ring

theorem eval_p_tlTTwoP5c3 (f x : ℚ) :
 (p_tlTTwoP5c3 f).eval x = MazurTorsion.Kubert.tlTTwoP5c3 f x := by
 simp only [p_tlTTwoP5c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c3
 ring

theorem eval_p_tlTTwoP5c4 (f x : ℚ) :
 (p_tlTTwoP5c4 f).eval x = MazurTorsion.Kubert.tlTTwoP5c4 f x := by
 simp only [p_tlTTwoP5c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c4
 ring

theorem eval_p_tlTTwoP5c5 (f x : ℚ) :
 (p_tlTTwoP5c5 f).eval x = MazurTorsion.Kubert.tlTTwoP5c5 f x := by
 simp only [p_tlTTwoP5c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c5
 ring

theorem eval_p_tlTTwoP5c6 (f x : ℚ) :
 (p_tlTTwoP5c6 f).eval x = MazurTorsion.Kubert.tlTTwoP5c6 f x := by
 simp only [p_tlTTwoP5c6, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c6
 ring

theorem eval_p_tlTTwoP5c7 (f x : ℚ) :
 (p_tlTTwoP5c7 f).eval x = MazurTorsion.Kubert.tlTTwoP5c7 f x := by
 simp only [p_tlTTwoP5c7, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c7
 ring

theorem eval_p_tlTTwoP5c8 (f x : ℚ) :
 (p_tlTTwoP5c8 f).eval x = MazurTorsion.Kubert.tlTTwoP5c8 f x := by
 simp only [p_tlTTwoP5c8, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c8
 ring

theorem eval_p_tlTTwoP5c9 (f x : ℚ) :
 (p_tlTTwoP5c9 f).eval x = MazurTorsion.Kubert.tlTTwoP5c9 f x := by
 simp only [p_tlTTwoP5c9, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c9
 ring

theorem eval_p_tlTTwoP5c10 (f x : ℚ) :
 (p_tlTTwoP5c10 f).eval x = MazurTorsion.Kubert.tlTTwoP5c10 f x := by
 simp only [p_tlTTwoP5c10, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c10
 ring

theorem eval_p_tlTTwoP5c11 (f x : ℚ) :
 (p_tlTTwoP5c11 f).eval x = MazurTorsion.Kubert.tlTTwoP5c11 f x := by
 simp only [p_tlTTwoP5c11, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c11
 ring

theorem eval_p_tlTTwoP5c12 (f x : ℚ) :
 (p_tlTTwoP5c12 f).eval x = MazurTorsion.Kubert.tlTTwoP5c12 f x := by
 simp only [p_tlTTwoP5c12, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c12
 ring

theorem eval_p_tlTTwoP5c13 (f x : ℚ) :
 (p_tlTTwoP5c13 f).eval x = MazurTorsion.Kubert.tlTTwoP5c13 f x := by
 simp only [p_tlTTwoP5c13, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoP5c13
 ring

theorem eval_p_tlTTwoQ5c0 (f x : ℚ) :
 (p_tlTTwoQ5c0 f).eval x = MazurTorsion.Kubert.tlTTwoQ5c0 f x := by
 simp only [p_tlTTwoQ5c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ5c0
 ring

theorem eval_p_tlTTwoQ5c1 (f x : ℚ) :
 (p_tlTTwoQ5c1 f).eval x = MazurTorsion.Kubert.tlTTwoQ5c1 f x := by
 simp only [p_tlTTwoQ5c1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ5c1
 ring

theorem eval_p_tlTTwoQ5c2 (f x : ℚ) :
 (p_tlTTwoQ5c2 f).eval x = MazurTorsion.Kubert.tlTTwoQ5c2 f x := by
 simp only [p_tlTTwoQ5c2, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ5c2
 ring

theorem eval_p_tlTTwoQ5c3 (f x : ℚ) :
 (p_tlTTwoQ5c3 f).eval x = MazurTorsion.Kubert.tlTTwoQ5c3 f x := by
 simp only [p_tlTTwoQ5c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ5c3
 ring

theorem eval_p_tlTTwoQ5c4 (f x : ℚ) :
 (p_tlTTwoQ5c4 f).eval x = MazurTorsion.Kubert.tlTTwoQ5c4 f x := by
 simp only [p_tlTTwoQ5c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ5c4
 ring

theorem eval_p_tlTTwoQ5c5 (f x : ℚ) :
 (p_tlTTwoQ5c5 f).eval x = MazurTorsion.Kubert.tlTTwoQ5c5 f x := by
 simp only [p_tlTTwoQ5c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ5c5
 ring

theorem eval_p_tlTTwoQ5c6 (f x : ℚ) :
 (p_tlTTwoQ5c6 f).eval x = MazurTorsion.Kubert.tlTTwoQ5c6 f x := by
 simp only [p_tlTTwoQ5c6, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlTTwoQ5c6
 ring

end MazurTransfer.Order27TTwo5Polynomial

#print axioms MazurTransfer.Order27TTwo5Polynomial.eval_p_tlNSqP1c7

open Polynomial MazurTorsion.Kubert MazurTransfer.Order27TTwo5Polynomial

theorem solution :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP1c7 f ξ + tlNSqP1c8 f ξ + tlNSqP1c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ) + (tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ)) +
        ((tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ) + (tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ))) +
        (((tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ) + (tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ)) +
        (tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ))) := by
 intro f ξ hT
 have h := congrArg (fun p : ℚ[X] => p.eval ξ) (MazurTransfer.order27_ttwo5_complete_polynomial_identity f)
 simp only [leftSide, rightSide, Polynomial.eval_add, Polynomial.eval_mul, eval_p_tlNSqP1c7, eval_p_tlNSqP1c8, eval_p_tlNSqP1c9, eval_p_tlD0, eval_p_tlD1, eval_p_tlT0, eval_p_tlT1, eval_p_tlT2, eval_p_tlT3, eval_p_tlTTwoP5c0, eval_p_tlTTwoP5c1, eval_p_tlTTwoP5c2, eval_p_tlTTwoP5c3, eval_p_tlTTwoP5c4, eval_p_tlTTwoP5c5, eval_p_tlTTwoP5c6, eval_p_tlTTwoP5c7, eval_p_tlTTwoP5c8, eval_p_tlTTwoP5c9, eval_p_tlTTwoP5c10, eval_p_tlTTwoP5c11, eval_p_tlTTwoP5c12, eval_p_tlTTwoP5c13, eval_p_tlTTwoQ5c0, eval_p_tlTTwoQ5c1, eval_p_tlTTwoQ5c2, eval_p_tlTTwoQ5c3, eval_p_tlTTwoQ5c4, eval_p_tlTTwoQ5c5, eval_p_tlTTwoQ5c6] at h
 rw [hT, mul_zero, add_zero] at h
 simpa only [add_assoc] using h

#print axioms solution
