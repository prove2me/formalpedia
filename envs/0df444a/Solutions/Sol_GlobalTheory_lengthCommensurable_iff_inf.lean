-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_iff_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:42.028327+00:00
-- url     : https://prove2.me/submissions/d4269281-a792-4483-af65-8edaf31d19f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}
namespace GlobalTheory
theorem _root_.solution :
    LengthCommensurable A B ↔
      LengthCommensurable A (A ⊓ B) ∧ LengthCommensurable B (A ⊓ B) := by
  rw [lengthCommensurable_iff_of_ge (inf_le_left : A ⊓ B ≤ A),
    lengthCommensurable_iff_of_ge (inf_le_right : A ⊓ B ≤ B),
    relLength_inf_right, relLength_inf_right', LengthCommensurable]
end GlobalTheory
