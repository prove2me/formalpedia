-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_integral_even_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:23:03.369684+00:00
-- url     : https://prove2.me/submissions/cddd8d45-fed6-4bc3-bbde-29c7b133db95

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

lemma fejer_integral_even_g_oai (k : ℕ) (hk : k ∈ Finset.Icc 1 127) :
    (∫ x, fejerPolynomial.eval x*(T ℝ (2*k)).eval x ∂measureT) =
      Real.pi/(1-(2*(k:ℝ))^2) := by
  have hk₀ : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  have hcast : (2*(k:ℤ)) ≠ 0 := by omega
  have he := fejer_weighted_orthogonal_g (2*k)
  push_cast at he
  rw [he]
  rw [integral_eval_T_real_measureT_of_ne_zero hcast]
  rw [Finset.sum_eq_single_of_mem k hk]
  · have hh := integral_T_real_mul_self_measureT_of_ne_zero (by omega : 2*k ≠ 0)
    push_cast at hh
    rw [hh]
    rw [show 1-(2*(k:ℝ))^2 = -(4*(k:ℝ)^2-1) by ring]
    simp only [div_neg]
    ring
  · intro a ha hne
    have hne' : 2*a ≠ 2*k := by omega
    have hh := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne'
    push_cast at hh
    rw [hh, mul_zero]

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_integral_even_g_oai := @OAI.SharpPlanar.fejer_integral_even_g_oai
