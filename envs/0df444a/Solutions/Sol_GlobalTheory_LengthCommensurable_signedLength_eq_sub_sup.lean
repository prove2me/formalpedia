-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_eq_sub_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:16.915021+00:00
-- url     : https://prove2.me/submissions/d01ae901-2a62-4d82-bfb7-03ef868780ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_lengthCommensurable_iff_sup

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
    signedLength A B = signedLength (A ⊔ B) B - signedLength (A ⊔ B) A := by
  obtain ⟨h₁, h₂⟩ := lengthCommensurable_iff_sup.mp h
  rw [h₁.signedLength_of_ge le_sup_right, h₂.signedLength_of_ge le_sup_left,
    relLength_sup_left, relLength_sup_left', signedLength]
end GlobalTheory.LengthCommensurable
