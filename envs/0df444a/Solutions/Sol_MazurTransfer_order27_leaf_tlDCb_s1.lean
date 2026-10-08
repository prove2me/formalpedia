-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlDCb_s1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:37:23.331593+00:00
-- url     : https://prove2.me/submissions/47e95b44-ee24-4be3-a0ed-3e0572d64a15

import Theorems.Thm_MazurTransfer_order27_dcb1_complete_polynomial_identity
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27DCb1PolynomialData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
namespace MazurTransfer.Order27DCb1Polynomial
open Polynomial

theorem eval_p_tlDSqP0c3 (f x : ℚ) :
 (p_tlDSqP0c3 f).eval x = MazurTorsion.Kubert.tlDSqP0c3 f x := by
 simp only [p_tlDSqP0c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDSqP0c3
 ring

theorem eval_p_tlDSqP0c4 (f x : ℚ) :
 (p_tlDSqP0c4 f).eval x = MazurTorsion.Kubert.tlDSqP0c4 f x := by
 simp only [p_tlDSqP0c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDSqP0c4
 ring

theorem eval_p_tlDSqP0c5 (f x : ℚ) :
 (p_tlDSqP0c5 f).eval x = MazurTorsion.Kubert.tlDSqP0c5 f x := by
 simp only [p_tlDSqP0c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDSqP0c5
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

theorem eval_p_tlDCbP1c0 (f x : ℚ) :
 (p_tlDCbP1c0 f).eval x = MazurTorsion.Kubert.tlDCbP1c0 f x := by
 simp only [p_tlDCbP1c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c0
 ring

theorem eval_p_tlDCbP1c1 (f x : ℚ) :
 (p_tlDCbP1c1 f).eval x = MazurTorsion.Kubert.tlDCbP1c1 f x := by
 simp only [p_tlDCbP1c1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c1
 ring

theorem eval_p_tlDCbP1c2 (f x : ℚ) :
 (p_tlDCbP1c2 f).eval x = MazurTorsion.Kubert.tlDCbP1c2 f x := by
 simp only [p_tlDCbP1c2, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c2
 ring

theorem eval_p_tlDCbP1c3 (f x : ℚ) :
 (p_tlDCbP1c3 f).eval x = MazurTorsion.Kubert.tlDCbP1c3 f x := by
 simp only [p_tlDCbP1c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c3
 ring

theorem eval_p_tlDCbP1c4 (f x : ℚ) :
 (p_tlDCbP1c4 f).eval x = MazurTorsion.Kubert.tlDCbP1c4 f x := by
 simp only [p_tlDCbP1c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c4
 ring

theorem eval_p_tlDCbP1c5 (f x : ℚ) :
 (p_tlDCbP1c5 f).eval x = MazurTorsion.Kubert.tlDCbP1c5 f x := by
 simp only [p_tlDCbP1c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c5
 ring

theorem eval_p_tlDCbP1c6 (f x : ℚ) :
 (p_tlDCbP1c6 f).eval x = MazurTorsion.Kubert.tlDCbP1c6 f x := by
 simp only [p_tlDCbP1c6, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c6
 ring

theorem eval_p_tlDCbP1c7 (f x : ℚ) :
 (p_tlDCbP1c7 f).eval x = MazurTorsion.Kubert.tlDCbP1c7 f x := by
 simp only [p_tlDCbP1c7, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c7
 ring

theorem eval_p_tlDCbP1c8 (f x : ℚ) :
 (p_tlDCbP1c8 f).eval x = MazurTorsion.Kubert.tlDCbP1c8 f x := by
 simp only [p_tlDCbP1c8, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c8
 ring

theorem eval_p_tlDCbP1c9 (f x : ℚ) :
 (p_tlDCbP1c9 f).eval x = MazurTorsion.Kubert.tlDCbP1c9 f x := by
 simp only [p_tlDCbP1c9, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c9
 ring

theorem eval_p_tlDCbP1c10 (f x : ℚ) :
 (p_tlDCbP1c10 f).eval x = MazurTorsion.Kubert.tlDCbP1c10 f x := by
 simp only [p_tlDCbP1c10, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c10
 ring

theorem eval_p_tlDCbP1c11 (f x : ℚ) :
 (p_tlDCbP1c11 f).eval x = MazurTorsion.Kubert.tlDCbP1c11 f x := by
 simp only [p_tlDCbP1c11, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c11
 ring

theorem eval_p_tlDCbP1c12 (f x : ℚ) :
 (p_tlDCbP1c12 f).eval x = MazurTorsion.Kubert.tlDCbP1c12 f x := by
 simp only [p_tlDCbP1c12, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbP1c12
 ring

theorem eval_p_tlDCbQ1c0 (f x : ℚ) :
 (p_tlDCbQ1c0 f).eval x = MazurTorsion.Kubert.tlDCbQ1c0 f x := by
 simp only [p_tlDCbQ1c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbQ1c0
 ring

theorem eval_p_tlDCbQ1c1 (f x : ℚ) :
 (p_tlDCbQ1c1 f).eval x = MazurTorsion.Kubert.tlDCbQ1c1 f x := by
 simp only [p_tlDCbQ1c1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbQ1c1
 ring

theorem eval_p_tlDCbQ1c2 (f x : ℚ) :
 (p_tlDCbQ1c2 f).eval x = MazurTorsion.Kubert.tlDCbQ1c2 f x := by
 simp only [p_tlDCbQ1c2, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbQ1c2
 ring

theorem eval_p_tlDCbQ1c3 (f x : ℚ) :
 (p_tlDCbQ1c3 f).eval x = MazurTorsion.Kubert.tlDCbQ1c3 f x := by
 simp only [p_tlDCbQ1c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbQ1c3
 ring

theorem eval_p_tlDCbQ1c4 (f x : ℚ) :
 (p_tlDCbQ1c4 f).eval x = MazurTorsion.Kubert.tlDCbQ1c4 f x := by
 simp only [p_tlDCbQ1c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbQ1c4
 ring

theorem eval_p_tlDCbQ1c5 (f x : ℚ) :
 (p_tlDCbQ1c5 f).eval x = MazurTorsion.Kubert.tlDCbQ1c5 f x := by
 simp only [p_tlDCbQ1c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlDCbQ1c5
 ring

end MazurTransfer.Order27DCb1Polynomial

#print axioms MazurTransfer.Order27DCb1Polynomial.eval_p_tlDSqP0c3

open Polynomial MazurTorsion.Kubert MazurTransfer.Order27DCb1Polynomial

theorem solution :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlDSqP0c3 f ξ + tlDSqP0c4 f ξ + tlDSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP1c0 f ξ + tlDCbP1c1 f ξ) + (tlDCbP1c2 f ξ + tlDCbP1c3 f ξ)) + ((tlDCbP1c4 f
        ξ + tlDCbP1c5 f ξ) + (tlDCbP1c6 f ξ + tlDCbP1c7 f ξ))) + (((tlDCbP1c8 f ξ +
        tlDCbP1c9 f ξ) + (tlDCbP1c10 f ξ + tlDCbP1c11 f ξ)) + tlDCbP1c12 f ξ)) := by
 intro f ξ hT
 have h := congrArg (fun p : ℚ[X] => p.eval ξ) (MazurTransfer.order27_dcb1_complete_polynomial_identity f)
 simp only [leftSide, rightSide, Polynomial.eval_add, Polynomial.eval_mul, eval_p_tlDSqP0c3, eval_p_tlDSqP0c4, eval_p_tlDSqP0c5, eval_p_tlD0, eval_p_tlD1, eval_p_tlT0, eval_p_tlT1, eval_p_tlT2, eval_p_tlT3, eval_p_tlDCbP1c0, eval_p_tlDCbP1c1, eval_p_tlDCbP1c2, eval_p_tlDCbP1c3, eval_p_tlDCbP1c4, eval_p_tlDCbP1c5, eval_p_tlDCbP1c6, eval_p_tlDCbP1c7, eval_p_tlDCbP1c8, eval_p_tlDCbP1c9, eval_p_tlDCbP1c10, eval_p_tlDCbP1c11, eval_p_tlDCbP1c12, eval_p_tlDCbQ1c0, eval_p_tlDCbQ1c1, eval_p_tlDCbQ1c2, eval_p_tlDCbQ1c3, eval_p_tlDCbQ1c4, eval_p_tlDCbQ1c5] at h
 rw [hT, mul_zero, add_zero] at h
 simpa only [add_assoc] using h

#print axioms solution
