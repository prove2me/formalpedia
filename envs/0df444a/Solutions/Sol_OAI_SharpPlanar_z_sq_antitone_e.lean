-- Prove2me | solution 1 for OAI.SharpPlanar.z_sq_antitone_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:23:34.726189+00:00
-- url     : https://prove2.me/submissions/fe69c511-d21b-4307-9393-844df44a2b7a

import Mathlib
import Definitions.Def_OAIQ098E001
import Theorems.Thm_OAI_SharpPlanar_z_sq_e

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


lemma z_sq_antitone_e_oai {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖z t‖^2 ≤ ‖z s‖^2 := by
  rw [z_sq_e,z_sq_e]
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by norm_num) (by unfold h; positivity)
  nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.z_sq_antitone_e_oai := @OAI.SharpPlanar.z_sq_antitone_e_oai
