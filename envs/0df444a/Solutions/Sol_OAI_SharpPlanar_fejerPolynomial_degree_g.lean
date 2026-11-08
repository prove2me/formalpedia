-- Prove2me | solution 1 for OAI.SharpPlanar.fejerPolynomial_degree_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:16:54.749642+00:00
-- url     : https://prove2.me/submissions/eaa4b2c6-f96b-426b-b9fa-13107eeb61d9

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

lemma fejerPolynomial_degree_g_oai : fejerPolynomial.degree ≤ 254 := by
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

theorem solution : type_of% @OAI.SharpPlanar.fejerPolynomial_degree_g_oai := @OAI.SharpPlanar.fejerPolynomial_degree_g_oai
