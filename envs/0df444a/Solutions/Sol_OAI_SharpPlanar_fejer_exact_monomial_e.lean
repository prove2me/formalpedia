-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_exact_monomial_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:42:26.249182+00:00
-- url     : https://prove2.me/submissions/3724dbbd-3b20-427d-8707-75761b81c7fb

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_fejer_exact_e

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

lemma fejer_exact_monomial_e_oai (k : ℕ) (hk : k < 256) :
    (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*(fejerNode v : ℂ)^k) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, (x:ℂ)^k) := by
  have h := fejer_exact_e (Polynomial.X^k) (by simpa using hk)
  simp only [eval_pow,eval_X] at h
  have hc := congrArg (fun x : ℝ => (x:ℂ)) h
  push_cast at hc
  simpa only [← Complex.ofReal_pow,intervalIntegral.integral_ofReal] using hc

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_exact_monomial_e_oai := @OAI.SharpPlanar.fejer_exact_monomial_e_oai
