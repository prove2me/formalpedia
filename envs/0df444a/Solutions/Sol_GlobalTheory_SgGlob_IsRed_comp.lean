-- Prove2me | solution 1 for GlobalTheory.SgGlob.IsRed.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:33.095871+00:00
-- url     : https://prove2.me/submissions/6559c70b-2cba-4314-b70c-372c9fd77fe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_form_mulVec
import Theorems.Thm_GlobalTheory_SgGlob_isUnit_det_of_isUn

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
omit [NumberField E]
namespace GlobalTheory.SgGlob
namespace IsRed
theorem _root_.solution {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E} {x y : Lz E m}
    {al : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (hJ : IsUnit Jb.det)
    {γ : Matrix (Fin m) (Fin m) E} (hγ : IsoLz σ Jb γ x y) : IsRed σ J Jb Λ P y (γ * al) := by
  have hu : IsUnit γ := (Matrix.isUnit_iff_isUnit_det γ).2 (isUnit_det_of_isUn hJ hγ.1)
  refine ⟨fun v hv => ?_, fun w => ?_, fun v hv w hw => ?_, ?_, ?_⟩
  · rw [← h.1 v hv, ← Matrix.mulVec_mulVec]
    exact ⟨fun e => Matrix.mulVec_injective_iff_isUnit.2 hu (e.trans (Matrix.mulVec_zero γ).symm),
      fun e => by rw [e, Matrix.mulVec_zero]⟩
  · obtain ⟨w', rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu w
    obtain ⟨v, hv, rfl⟩ := h.2.1 w'
    exact ⟨v, hv, (Matrix.mulVec_mulVec _ _ _).symm⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, form_mulVec hγ.1, h.2.2.1 v hv w hw]
  · rw [← hγ.2.1, ← h.2.2.2.1, latMap, ← Submodule.map_comp, Matrix.mulVecLin_mul]
    rfl
  · rw [← Matrix.mulVec_mulVec, h.2.2.2.2, hγ.2.2]
end IsRed
end GlobalTheory.SgGlob
