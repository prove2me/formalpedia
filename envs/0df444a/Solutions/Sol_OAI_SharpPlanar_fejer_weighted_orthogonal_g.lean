-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_weighted_orthogonal_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:21:33.501971+00:00
-- url     : https://prove2.me/submissions/a3879e1d-052f-4cf2-9560-c7f2670e5d4b

import Mathlib
import Definitions.Def_OAIQ098G072

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

lemma fejer_weighted_orthogonal_g_oai (n : ℕ) :
    (∫ x, fejerPolynomial.eval x*(T ℝ n).eval x ∂measureT) =
      (∫ x, (T ℝ n).eval x ∂measureT) -
      ∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1))*
        (∫ x, (T ℝ (2*a)).eval x*(T ℝ n).eval x ∂measureT) := by
  unfold fejerPolynomial
  simp only [eval_sub, eval_one, eval_finsetSum, eval_smul, smul_eq_mul,
    sub_mul, one_mul, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_sub (integrable_measureT (by fun_prop))
    (integrable_measureT (by fun_prop)), MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
  · intro a ha
    exact integrable_measureT (by fun_prop)

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_weighted_orthogonal_g_oai := @OAI.SharpPlanar.fejer_weighted_orthogonal_g_oai
