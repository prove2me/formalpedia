-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_integral_odd_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:21:24.359209+00:00
-- url     : https://prove2.me/submissions/c787c6bb-68a6-4789-aed9-543034c76069

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

lemma fejer_integral_odd_g_oai (k : ℕ) :
    (∫ x, fejerPolynomial.eval x*(T ℝ (2*k+1)).eval x ∂measureT) = 0 := by
  have hh := fejer_weighted_orthogonal_g (2*k+1)
  push_cast at hh
  rw [hh, integral_eval_T_real_measureT_of_ne_zero (by omega : (2*(k:ℤ)+1) ≠ 0)]
  have he : (∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1))*
      (∫ x, (T ℝ (2*a)).eval x*(T ℝ (2*k+1)).eval x ∂measureT)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hne : 2*a ≠ 2*k+1 := by omega
    have h := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne
    push_cast at h
    rw [h, mul_zero]
  rw [he, sub_self]

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_integral_odd_g_oai := @OAI.SharpPlanar.fejer_integral_odd_g_oai
