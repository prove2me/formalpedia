-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_integral_zero_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:23:08.859523+00:00
-- url     : https://prove2.me/submissions/33f1550c-1d50-4389-8963-a2a18111da74

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_fejer_weighted_orthogonal_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma fejer_integral_zero_g_oai :
    (∫ x, fejerPolynomial.eval x*(T ℝ 0).eval x ∂measureT) = Real.pi := by
  change (∫ x, fejerPolynomial.eval x*(T ℝ (0:ℕ)).eval x ∂measureT) = _
  rw [fejer_weighted_orthogonal_g 0]
  norm_num only [Nat.cast_zero] at *
  rw [integral_eval_T_real_measureT_zero]
  simp only [sub_eq_self]
  apply Finset.sum_eq_zero
  intro a ha
  have hne : 2*a ≠ (0:ℕ) := by have := (Finset.mem_Icc.mp ha).1; omega
  have h := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne
  push_cast at h
  rw [h, mul_zero]

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_integral_zero_g_oai := @OAI.SharpPlanar.fejer_integral_zero_g_oai
