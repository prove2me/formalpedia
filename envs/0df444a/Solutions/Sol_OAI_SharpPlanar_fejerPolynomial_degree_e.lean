-- Prove2me | solution 1 for OAI.SharpPlanar.fejerPolynomial_degree_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:39:26.564159+00:00
-- url     : https://prove2.me/submissions/f94889fe-e8c1-4b04-8ae0-a8fd98ae946d

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

lemma fejerPolynomial_degree_e_oai : fejerPolynomial.degree ≤ 254 := by
  apply (degree_sub_le _ _).trans
  apply max_le
  · norm_num
  · apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro a ha
    apply (degree_smul_le _ _).trans
    rw [degree_T]
    have ha' := (Finset.mem_Icc.mp ha).2
    norm_cast
    omega

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejerPolynomial_degree_e_oai := @OAI.SharpPlanar.fejerPolynomial_degree_e_oai
