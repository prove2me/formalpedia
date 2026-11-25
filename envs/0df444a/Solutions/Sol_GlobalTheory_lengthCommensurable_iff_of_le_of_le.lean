-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_iff_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:25.518177+00:00
-- url     : https://prove2.me/submissions/8a2ac389-d52c-4d17-90d2-c959ad847403

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable {A A' B B' C : Submodule R V}
namespace GlobalTheory
theorem _root_.solution (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A C ↔ LengthCommensurable A B ∧ LengthCommensurable B C := by
  rw [lengthCommensurable_iff_of_ge hCB, lengthCommensurable_iff_of_ge hBA,
    lengthCommensurable_iff_of_ge (hCB.trans hBA), relLength_eq_add_of_le hCB hBA]
  exact WithTop.add_ne_top
end GlobalTheory
