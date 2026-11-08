-- Prove2me | solution 1 for OAI.SharpPlanar.taylorPolynomial_zero_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:26:42.104099+00:00
-- url     : https://prove2.me/submissions/630bd633-678a-4943-9d67-2e1a99fd4f38

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



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory Set

lemma taylorPolynomial_zero_g_oai (f : ℂ → ℂ) (N : ℕ) :
    taylorPolynomial f 0 N = fun z =>
      ∑ k ∈ Finset.range N, ((k.factorial:ℂ)⁻¹*iteratedDeriv k f 0)*z^k := by
  funext z
  simp only [taylorPolynomial,sub_zero]

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.taylorPolynomial_zero_g_oai := @OAI.SharpPlanar.taylorPolynomial_zero_g_oai
