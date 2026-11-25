-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:29:30.212358+00:00
-- url     : https://prove2.me/submissions/5555291b-60fe-4f7e-b453-7ebd753348ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_inf_right
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_eq_toNat_sub_of_le

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
theorem _root_.solution (hAB : LengthCommensurable A B) (hBC : LengthCommensurable B C) :
    signedLength A C = signedLength A B + signedLength B C := by
  have hAC := hAB.trans hBC
  have hAD : LengthCommensurable A (A ⊓ B ⊓ C) := ((refl A).inf_right hAB).inf_right hAC
  have hA : A ⊓ B ⊓ C ≤ A := inf_le_left.trans inf_le_left
  have hB : A ⊓ B ⊓ C ≤ B := inf_le_left.trans inf_le_right
  have hC : A ⊓ B ⊓ C ≤ C := inf_le_right
  rw [hAB.signedLength_eq_toNat_sub_of_le hAD hA hB, hAC.signedLength_eq_toNat_sub_of_le hAD hA hC,
    hBC.signedLength_eq_toNat_sub_of_le (hAB.symm.trans hAD) hB hC]
  ring
end GlobalTheory.LengthCommensurable
