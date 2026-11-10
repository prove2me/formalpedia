-- Prove2me | solution 1 for OAI.SharpPlanar.piece_secant_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:22:37.015208+00:00
-- url     : https://prove2.me/submissions/434d3373-542d-49dc-9555-863f26a763ff

import Mathlib
import Definitions.Def_OAIQ098G362

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma piece_secant_bound_g_oai (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    slopeCap j*(t^2+h^2)*((((j.val:ℝ)+1)/6)^2+h^2) ≤
      h*B*(t+((j.val:ℝ)+1)/6) := by
  have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
  fin_cases j <;> norm_num [slopeCap,h,B] at * <;> nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.piece_secant_bound_g_oai := @OAI.SharpPlanar.piece_secant_bound_g_oai
