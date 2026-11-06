-- Prove2me | solution 1 for OAI.SharpPlanar.taylorPolynomial_zero_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:47:14.386059+00:00
-- url     : https://prove2.me/submissions/4779015d-eaef-47ad-ba9f-c23c7c25ed43

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



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory Set

lemma taylorPolynomial_zero_e_oai (f : ℂ → ℂ) (N : ℕ) :
    taylorPolynomial f 0 N = fun z =>
      ∑ k ∈ Finset.range N, ((k.factorial:ℂ)⁻¹*iteratedDeriv k f 0)*z^k := by
  funext z
  simp only [taylorPolynomial,sub_zero]

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.taylorPolynomial_zero_e_oai := @OAI.SharpPlanar.taylorPolynomial_zero_e_oai
