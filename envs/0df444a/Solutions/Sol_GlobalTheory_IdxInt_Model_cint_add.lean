-- Prove2me | solution 1 for GlobalTheory.IdxInt.Model.cint_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:50:15.532558+00:00
-- url     : https://prove2.me/submissions/477770cb-b070-4b46-bf45-36294c28abe0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Theorems.Thm_GlobalTheory_IdxInt_Model_supp_fin
import Theorems.Thm_GlobalTheory_IdxInt_Model_cint_eq
import Theorems.Thm_GlobalTheory_IdxInt_Model_fine_refine

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
theorem _root_.solution {A : AddSubgroup W} {φ ψ : W → ℂ} (h : Nice A φ) (h' : Nice A ψ) :
    Nice A (φ + ψ) ∧ cint A (φ + ψ) = cint A φ + cint A ψ := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨B', hB'⟩ := h'
  have hC : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB'.2.1
  have f1 := fine_refine hB inf_le_left hC
  have f2 := fine_refine hB' inf_le_right hC
  have f3 : Fine A (φ + ψ) (B ⊓ B') := by
    refine ⟨f1.1, hC, fun w b hb => by simp [f1.2.2.1 w b hb, f2.2.2.1 w b hb], ?_⟩
    refine (f1.2.2.2.union f2.2.2.2).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    rcases Function.support_add φ ψ hw with h | h
    · exact Or.inl ⟨w, h, rfl⟩
    · exact Or.inr ⟨w, h, rfl⟩
  refine ⟨⟨_, f3⟩, ?_⟩
  rw [cint_eq f1, cint_eq f2, cint_eq f3, ← add_div, ← finsum_add_distrib (supp_fin f1) (supp_fin f2)]
  rfl
end GlobalTheory.IdxInt.Model
