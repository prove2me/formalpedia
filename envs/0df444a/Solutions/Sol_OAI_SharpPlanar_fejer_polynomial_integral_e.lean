-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_polynomial_integral_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:43:56.301799+00:00
-- url     : https://prove2.me/submissions/76e74728-deb3-450b-b692-a40c12b9c094

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_fejer_cheb_integral_e

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

lemma fejer_polynomial_integral_e_oai (P : ℝ[X]) (hP : P.degree < 256) :
    (∫ x, fejerPolynomial.eval x * P.eval x ∂measureT) =
      (Real.pi/2)*(∫ x in (-1:ℝ)..1, P.eval x) := by
  have hmem : P ∈ degreeLT ℝ 256 := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio 256 = Finset.range 256 by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum, intervalIntegral.integral_finsetSum]
  · simp_rw [mul_left_comm (fejerPolynomial.eval _) (c _),
      MeasureTheory.integral_const_mul, intervalIntegral.integral_const_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (chebyshevTsequence ℝ n) = T ℝ n by rfl,
      fejer_cheb_integral_e n (Finset.mem_range.mp hn)]
    ring
  · intro n hn
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro n hn
    exact integrable_measureT (by fun_prop)

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_polynomial_integral_e_oai := @OAI.SharpPlanar.fejer_polynomial_integral_e_oai
