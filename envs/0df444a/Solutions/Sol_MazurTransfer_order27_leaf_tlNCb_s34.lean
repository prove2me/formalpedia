-- Prove2me | solution 1 for MazurTransfer.order27_leaf_tlNCb_s34
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:37:43.437392+00:00
-- url     : https://prove2.me/submissions/b04a7ba8-6a1a-4cad-ad64-03de6a30031f

import Theorems.Thm_MazurTransfer_order27_ncb34_complete_polynomial_identity
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27NCb34PolynomialData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
namespace MazurTransfer.Order27NCb34Polynomial
open Polynomial

theorem eval_p_tlNSqP3c5 (f x : ℚ) :
 (p_tlNSqP3c5 f).eval x = MazurTorsion.Kubert.tlNSqP3c5 f x := by
 simp only [p_tlNSqP3c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNSqP3c5
 ring

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

theorem eval_p_tlNCbP34c0 (f x : ℚ) :
 (p_tlNCbP34c0 f).eval x = MazurTorsion.Kubert.tlNCbP34c0 f x := by
 simp only [p_tlNCbP34c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c0
 ring

theorem eval_p_tlNCbP34c1 (f x : ℚ) :
 (p_tlNCbP34c1 f).eval x = MazurTorsion.Kubert.tlNCbP34c1 f x := by
 simp only [p_tlNCbP34c1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c1
 ring

theorem eval_p_tlNCbP34c2 (f x : ℚ) :
 (p_tlNCbP34c2 f).eval x = MazurTorsion.Kubert.tlNCbP34c2 f x := by
 simp only [p_tlNCbP34c2, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c2
 ring

theorem eval_p_tlNCbP34c3 (f x : ℚ) :
 (p_tlNCbP34c3 f).eval x = MazurTorsion.Kubert.tlNCbP34c3 f x := by
 simp only [p_tlNCbP34c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c3
 ring

theorem eval_p_tlNCbP34c4 (f x : ℚ) :
 (p_tlNCbP34c4 f).eval x = MazurTorsion.Kubert.tlNCbP34c4 f x := by
 simp only [p_tlNCbP34c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c4
 ring

theorem eval_p_tlNCbP34c5 (f x : ℚ) :
 (p_tlNCbP34c5 f).eval x = MazurTorsion.Kubert.tlNCbP34c5 f x := by
 simp only [p_tlNCbP34c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c5
 ring

theorem eval_p_tlNCbP34c6 (f x : ℚ) :
 (p_tlNCbP34c6 f).eval x = MazurTorsion.Kubert.tlNCbP34c6 f x := by
 simp only [p_tlNCbP34c6, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c6
 ring

theorem eval_p_tlNCbP34c7 (f x : ℚ) :
 (p_tlNCbP34c7 f).eval x = MazurTorsion.Kubert.tlNCbP34c7 f x := by
 simp only [p_tlNCbP34c7, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c7
 ring

theorem eval_p_tlNCbP34c8 (f x : ℚ) :
 (p_tlNCbP34c8 f).eval x = MazurTorsion.Kubert.tlNCbP34c8 f x := by
 simp only [p_tlNCbP34c8, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c8
 ring

theorem eval_p_tlNCbP34c9 (f x : ℚ) :
 (p_tlNCbP34c9 f).eval x = MazurTorsion.Kubert.tlNCbP34c9 f x := by
 simp only [p_tlNCbP34c9, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c9
 ring

theorem eval_p_tlNCbP34c10 (f x : ℚ) :
 (p_tlNCbP34c10 f).eval x = MazurTorsion.Kubert.tlNCbP34c10 f x := by
 simp only [p_tlNCbP34c10, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c10
 ring

theorem eval_p_tlNCbP34c11 (f x : ℚ) :
 (p_tlNCbP34c11 f).eval x = MazurTorsion.Kubert.tlNCbP34c11 f x := by
 simp only [p_tlNCbP34c11, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c11
 ring

theorem eval_p_tlNCbP34c12 (f x : ℚ) :
 (p_tlNCbP34c12 f).eval x = MazurTorsion.Kubert.tlNCbP34c12 f x := by
 simp only [p_tlNCbP34c12, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c12
 ring

theorem eval_p_tlNCbP34c13 (f x : ℚ) :
 (p_tlNCbP34c13 f).eval x = MazurTorsion.Kubert.tlNCbP34c13 f x := by
 simp only [p_tlNCbP34c13, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c13
 ring

theorem eval_p_tlNCbP34c14 (f x : ℚ) :
 (p_tlNCbP34c14 f).eval x = MazurTorsion.Kubert.tlNCbP34c14 f x := by
 simp only [p_tlNCbP34c14, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c14
 ring

theorem eval_p_tlNCbP34c15 (f x : ℚ) :
 (p_tlNCbP34c15 f).eval x = MazurTorsion.Kubert.tlNCbP34c15 f x := by
 simp only [p_tlNCbP34c15, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c15
 ring

theorem eval_p_tlNCbP34c16 (f x : ℚ) :
 (p_tlNCbP34c16 f).eval x = MazurTorsion.Kubert.tlNCbP34c16 f x := by
 simp only [p_tlNCbP34c16, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c16
 ring

theorem eval_p_tlNCbP34c17 (f x : ℚ) :
 (p_tlNCbP34c17 f).eval x = MazurTorsion.Kubert.tlNCbP34c17 f x := by
 simp only [p_tlNCbP34c17, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbP34c17
 ring

theorem eval_p_tlNCbQ34c0 (f x : ℚ) :
 (p_tlNCbQ34c0 f).eval x = MazurTorsion.Kubert.tlNCbQ34c0 f x := by
 simp only [p_tlNCbQ34c0, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbQ34c0
 ring

theorem eval_p_tlNCbQ34c1 (f x : ℚ) :
 (p_tlNCbQ34c1 f).eval x = MazurTorsion.Kubert.tlNCbQ34c1 f x := by
 simp only [p_tlNCbQ34c1, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbQ34c1
 ring

theorem eval_p_tlNCbQ34c2 (f x : ℚ) :
 (p_tlNCbQ34c2 f).eval x = MazurTorsion.Kubert.tlNCbQ34c2 f x := by
 simp only [p_tlNCbQ34c2, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbQ34c2
 ring

theorem eval_p_tlNCbQ34c3 (f x : ℚ) :
 (p_tlNCbQ34c3 f).eval x = MazurTorsion.Kubert.tlNCbQ34c3 f x := by
 simp only [p_tlNCbQ34c3, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbQ34c3
 ring

theorem eval_p_tlNCbQ34c4 (f x : ℚ) :
 (p_tlNCbQ34c4 f).eval x = MazurTorsion.Kubert.tlNCbQ34c4 f x := by
 simp only [p_tlNCbQ34c4, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbQ34c4
 ring

theorem eval_p_tlNCbQ34c5 (f x : ℚ) :
 (p_tlNCbQ34c5 f).eval x = MazurTorsion.Kubert.tlNCbQ34c5 f x := by
 simp only [p_tlNCbQ34c5, Polynomial.eval_add, Polynomial.eval_monomial]
 unfold MazurTorsion.Kubert.tlNCbQ34c5
 ring

end MazurTransfer.Order27NCb34Polynomial

#print axioms MazurTransfer.Order27NCb34Polynomial.eval_p_tlNSqP3c5

open Polynomial MazurTorsion.Kubert MazurTransfer.Order27NCb34Polynomial

theorem solution :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
(tlNSqP3c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP34c0 f ξ + tlNCbP34c1 f ξ) + (tlNCbP34c2 f ξ + tlNCbP34c3 f ξ)) +
        ((tlNCbP34c4 f ξ + tlNCbP34c5 f ξ) + (tlNCbP34c6 f ξ + tlNCbP34c7 f ξ))) +
        (((tlNCbP34c8 f ξ + tlNCbP34c9 f ξ) + (tlNCbP34c10 f ξ + tlNCbP34c11 f ξ)) +
        ((tlNCbP34c12 f ξ + tlNCbP34c13 f ξ) + (tlNCbP34c14 f ξ + tlNCbP34c15 f ξ)))) +
        (tlNCbP34c16 f ξ + tlNCbP34c17 f ξ)) := by
 intro f ξ hT
 have h := congrArg (fun p : ℚ[X] => p.eval ξ) (MazurTransfer.order27_ncb34_complete_polynomial_identity f)
 simp only [leftSide, rightSide, Polynomial.eval_add, Polynomial.eval_mul, eval_p_tlNSqP3c5, eval_p_tlN0, eval_p_tlN1, eval_p_tlN2, eval_p_tlN3, eval_p_tlT0, eval_p_tlT1, eval_p_tlT2, eval_p_tlT3, eval_p_tlNCbP34c0, eval_p_tlNCbP34c1, eval_p_tlNCbP34c2, eval_p_tlNCbP34c3, eval_p_tlNCbP34c4, eval_p_tlNCbP34c5, eval_p_tlNCbP34c6, eval_p_tlNCbP34c7, eval_p_tlNCbP34c8, eval_p_tlNCbP34c9, eval_p_tlNCbP34c10, eval_p_tlNCbP34c11, eval_p_tlNCbP34c12, eval_p_tlNCbP34c13, eval_p_tlNCbP34c14, eval_p_tlNCbP34c15, eval_p_tlNCbP34c16, eval_p_tlNCbP34c17, eval_p_tlNCbQ34c0, eval_p_tlNCbQ34c1, eval_p_tlNCbQ34c2, eval_p_tlNCbQ34c3, eval_p_tlNCbQ34c4, eval_p_tlNCbQ34c5] at h
 rw [hT, mul_zero, add_zero] at h
 simpa only [add_assoc] using h

#print axioms solution
