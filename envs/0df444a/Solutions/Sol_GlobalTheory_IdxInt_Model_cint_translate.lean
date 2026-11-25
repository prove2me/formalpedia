-- Prove2me | solution 1 for GlobalTheory.IdxInt.Model.cint_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:34.809349+00:00
-- url     : https://prove2.me/submissions/08d2bf7f-eec5-449c-a5e8-9c49b5488a36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Theorems.Thm_GlobalTheory_IdxInt_Model_out_mk
import Theorems.Thm_GlobalTheory_IdxInt_Model_cint_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt
variable {W : Type} [AddCommGroup W]
namespace GlobalTheory.IdxInt.Model
theorem _root_.solution {A : AddSubgroup W} {φ : W → ℂ} (h : Nice A φ) (t : W) :
    cint A (fun w => φ (t + w)) = cint A φ := by
  obtain ⟨B, hB⟩ := h
  have hB' : Fine A (fun w => φ (t + w)) B := by
    refine ⟨hB.1, hB.2.1, fun w b hb => by simp only [← add_assoc]; exact hB.2.2.1 _ b hb, ?_⟩
    refine (hB.2.2.2.image (fun c => -(QuotientAddGroup.mk t : W ⧸ B) + c)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, ⟨t + w, hw, rfl⟩, by simp⟩
  rw [cint_eq hB, cint_eq hB']
  congr 1
  rw [← finsum_comp_equiv (Equiv.addLeft (QuotientAddGroup.mk t : W ⧸ B)) (f := fun c : W ⧸ B => φ c.out)]
  refine finsum_congr fun c => ?_
  have : (Equiv.addLeft (QuotientAddGroup.mk t : W ⧸ B)) c = QuotientAddGroup.mk (t + c.out) := by
    simp
  rw [this, out_mk hB.2.2.1]
end GlobalTheory.IdxInt.Model
