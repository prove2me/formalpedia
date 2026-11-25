-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_eq_toNat_sub_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:18.735472+00:00
-- url     : https://prove2.me/submissions/3d5cee95-6b4b-4ab5-a625-6352723057b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_toNat_relLength_eq_add_of_le

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
open GlobalTheory.LengthCommensurable
namespace GlobalTheory.LengthCommensurable
theorem _root_.solution {D : Submodule R V} (h : LengthCommensurable A B)
    (hAD : LengthCommensurable A D) (hDA : D ≤ A) (hDB : D ≤ B) :
    signedLength A B = ((relLength A D).toNat : ℤ) - ((relLength B D).toNat : ℤ) := by
  have hBD : LengthCommensurable B D := h.symm.trans hAD
  have h₁ := hAD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_left
  have h₂ := hBD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_right
  rw [relLength_inf_right] at h₁
  rw [relLength_inf_right'] at h₂
  rw [h₁, h₂, signedLength]
  push_cast
  ring
end GlobalTheory.LengthCommensurable
