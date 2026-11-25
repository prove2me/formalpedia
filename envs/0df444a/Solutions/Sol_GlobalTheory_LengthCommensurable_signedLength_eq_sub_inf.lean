-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_eq_sub_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:10.81492+00:00
-- url     : https://prove2.me/submissions/736b6694-0b71-4970-9223-8aff541a1d99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_lengthCommensurable_iff_inf

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
open GlobalTheory.LengthCommensurable
namespace GlobalTheory.LengthCommensurable
theorem _root_.solution (h : LengthCommensurable A B) :
    signedLength A B = signedLength A (A ⊓ B) - signedLength B (A ⊓ B) := by
  obtain ⟨h₁, h₂⟩ := lengthCommensurable_iff_inf.mp h
  rw [h₁.signedLength_of_ge inf_le_left, h₂.signedLength_of_ge inf_le_right,
    relLength_inf_right, relLength_inf_right', signedLength]
end GlobalTheory.LengthCommensurable
