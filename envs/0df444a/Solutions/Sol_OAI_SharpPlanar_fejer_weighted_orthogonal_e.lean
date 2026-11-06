-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_weighted_orthogonal_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:44:18.306135+00:00
-- url     : https://prove2.me/submissions/009116f0-c139-4141-9fa6-d0593277683a

import Mathlib
import Definitions.Def_OAIQ098E018

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

lemma fejer_weighted_orthogonal_e_oai (n : ℕ) :
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

theorem solution : type_of% @OAI.SharpPlanar.fejer_weighted_orthogonal_e_oai := @OAI.SharpPlanar.fejer_weighted_orthogonal_e_oai
