-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_exact_complex_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:20:57.742204+00:00
-- url     : https://prove2.me/submissions/2d238727-893c-47dc-811c-38327d6e807a

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_fejer_exact_monomial_g

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

lemma fejer_exact_complex_g_oai (c : ℕ → ℂ) :
    (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*
      (∑ k ∈ Finset.range 256, c k*(fejerNode v : ℂ)^k)) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, ∑ k ∈ Finset.range 256, c k*(x:ℂ)^k) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = c k * ∑ v ∈ Finset.range 256,
          (fejerWeight v : ℂ)*(fejerNode v : ℂ)^k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = _ := by rw [fejer_exact_monomial_g k (Finset.mem_range.mp hk)]; ring
  · intro k hk
    exact Continuous.intervalIntegrable (by fun_prop) _ _

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_exact_complex_g_oai := @OAI.SharpPlanar.fejer_exact_complex_g_oai
