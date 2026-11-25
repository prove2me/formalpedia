-- Prove2me | solution 1 for GlobalTheory.SgGlob.IsRed.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:09.271227+00:00
-- url     : https://prove2.me/submissions/47e3c7a6-8618-48c4-8220-2fa26fecd07d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_mem_spanX
import Theorems.Thm_GlobalTheory_SgGlob_IsRed_mem_iff
import Theorems.Thm_GlobalTheory_SgGlob_zOf_mem_perpX
import Theorems.Thm_GlobalTheory_SgGlob_form_mulVec
import Theorems.Thm_GlobalTheory_SgGlob_isUnit_det_of_isUn
import Theorems.Thm_GlobalTheory_SgGlob_mulVec_mem_perpX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
namespace GlobalTheory.SgGlob
namespace IsRed
theorem _root_.solution (hJ : IsUnit J.det) {T : E} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {P : Matrix (Fin n) (Fin (r + 1)) E} {x : Lz E m} {al bl : Matrix (Fin m) (Fin n) E}
    (h : IsRed σ J Jb Λ P x al) (hP : IsFrame σ J T P) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ)
    (hb : ∀ v ∈ perpX σ J P, bl *ᵥ (γ *ᵥ v) = al *ᵥ v) : IsRed σ J Jb (latMap γ Λ) (γ * P) x bl := by
  have hu : IsUnit γ := (Matrix.isUnit_iff_isUnit_det γ).2 (isUnit_det_of_isUn hJ hγ)
  have hs := Matrix.mulVec_surjective_iff_isUnit.2 hu
  have he : eOf (γ * P) = γ * eOf P := rfl
  refine ⟨fun v hv => ?_, fun y => ?_, fun v hv w hw => ?_, ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := hs v
    rw [mulVec_mem_perpX hγ] at hv
    rw [hb v hv, h.1 v hv, mem_spanX, mem_spanX, he]
    refine exists_congr fun c => ?_
    rw [← Matrix.mulVec_mulVec]
    exact (Matrix.mulVec_injective_iff_isUnit.2 hu).eq_iff.symm
  · obtain ⟨v, hv, rfl⟩ := h.2.1 y
    exact ⟨_, (mulVec_mem_perpX hγ P v).2 hv, hb v hv⟩
  · obtain ⟨v, rfl⟩ := hs v
    obtain ⟨w, rfl⟩ := hs w
    rw [mulVec_mem_perpX hγ] at hv hw
    rw [hb v hv, hb w hw, h.2.2.1 v hv w hw, form_mulVec hγ]
  · ext y
    rw [h.mem_iff]
    constructor
    · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hv'⟩, rfl⟩
      have hv'' := (mulVec_mem_perpX hγ P v).1 hv'
      exact ⟨v, ⟨hv, hv''⟩, (hb v hv'').symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨γ *ᵥ v, ⟨⟨v, hv.1, rfl⟩, (mulVec_mem_perpX hγ P v).2 hv.2⟩, hb v hv.2⟩
  · exact (hb _ (zOf_mem_perpX hP)).trans h.2.2.2.2
end IsRed
end GlobalTheory.SgGlob
