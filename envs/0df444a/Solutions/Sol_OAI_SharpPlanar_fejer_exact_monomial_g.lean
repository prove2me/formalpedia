-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_exact_monomial_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:21:16.12167+00:00
-- url     : https://prove2.me/submissions/8383587f-044e-453d-a53c-666fac86efb6

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_fejer_exact_g

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

lemma fejer_exact_monomial_g_oai (k : ℕ) (hk : k < 256) :
    (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*(fejerNode v : ℂ)^k) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, (x:ℂ)^k) := by
  have h := fejer_exact_g (Polynomial.X^k) (by simpa using hk)
  simp only [eval_pow,eval_X] at h
  have hc := congrArg (fun x : ℝ => (x:ℂ)) h
  push_cast at hc
  simpa only [← Complex.ofReal_pow,intervalIntegral.integral_ofReal] using hc

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_exact_monomial_g_oai := @OAI.SharpPlanar.fejer_exact_monomial_g_oai
