-- Prove2me | solution 1 for OAI.SharpPlanar.fejerPolynomial_eval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:40:10.263987+00:00
-- url     : https://prove2.me/submissions/8a8da671-a083-4326-9960-8218cf2fb895

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

lemma fejerPolynomial_eval_e_oai (v : ℕ) :
    fejerPolynomial.eval (fejerNode v) = 256*fejerWeight v := by
  unfold fejerPolynomial
  rw [eval_sub, eval_one, eval_finsetSum]
  simp only [eval_smul, smul_eq_mul, fejerNode, T_real_cos]
  unfold fejerWeight
  simp only [Finset.mul_sum]
  push_cast
  rw [show ∀ x : ℝ, 256*(x/256)=x from fun x => by ring]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejerPolynomial_eval_e_oai := @OAI.SharpPlanar.fejerPolynomial_eval_e_oai
