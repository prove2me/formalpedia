-- Prove2me | solution 1 for OAI.SharpPlanar.z_sq_antitone_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:51:55.202485+00:00
-- url     : https://prove2.me/submissions/550f9fbd-349e-48a9-9351-fc8d75b4749d

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_z_sq_g

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


lemma z_sq_antitone_g_oai {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖z t‖^2 ≤ ‖z s‖^2 := by
  rw [z_sq_g,z_sq_g]
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by norm_num) (by unfold h; positivity)
  nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.z_sq_antitone_g_oai := @OAI.SharpPlanar.z_sq_antitone_g_oai
