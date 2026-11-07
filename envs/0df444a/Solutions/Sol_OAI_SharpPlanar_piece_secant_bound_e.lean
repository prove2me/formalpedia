-- Prove2me | solution 1 for OAI.SharpPlanar.piece_secant_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:24:01.418908+00:00
-- url     : https://prove2.me/submissions/68bcca0f-646e-4036-82a4-2efbba202a7a

import Mathlib
import Definitions.Def_OAIQ098E125

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


lemma piece_secant_bound_e_oai (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    slopeCap j*(t^2+h^2)*((((j.val:ℝ)+1)/6)^2+h^2) ≤
      h*B*(t+((j.val:ℝ)+1)/6) := by
  have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
  fin_cases j <;> norm_num [slopeCap,h,B] at * <;> nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.piece_secant_bound_e_oai := @OAI.SharpPlanar.piece_secant_bound_e_oai
