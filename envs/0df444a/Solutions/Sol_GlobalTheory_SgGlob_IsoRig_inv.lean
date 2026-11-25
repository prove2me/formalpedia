-- Prove2me | solution 1 for GlobalTheory.SgGlob.IsoRig.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:38.178935+00:00
-- url     : https://prove2.me/submissions/55ee6db6-3981-44c5-9041-e39bbe98d8fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_isUnit_det_of_isUn
import Theorems.Thm_GlobalTheory_SgGlob_mulVec_mem_perpX
import Theorems.Thm_GlobalTheory_SgGlob_isUn_of_mul_eq_one
import Theorems.Thm_GlobalTheory_SgGlob_latMap_one
import Theorems.Thm_GlobalTheory_SgGlob_latMap_mul

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
namespace IsoRig
theorem _root_.solution (hJ : IsUnit J.det) {γ : Matrix (Fin n) (Fin n) E} {c d : Rig E n m r}
    (h : IsoRig σ J γ c d) : IsoRig σ J γ⁻¹ d c := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
  have hu := isUnit_det_of_isUn hJ h1
  have l := Matrix.nonsing_inv_mul γ hu
  have s := Matrix.mul_nonsing_inv γ hu
  have e (v : Fin n → E) : γ *ᵥ (γ⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, s, Matrix.one_mulVec]
  refine ⟨⟨isUn_of_mul_eq_one h1 s, by rw [← h2, ← latMap_mul, l, latMap_one],
    by rw [← h3, ← Matrix.mul_assoc, l, Matrix.one_mul],
    by rw [← h4, ← Matrix.mul_assoc, l, Matrix.one_mul]⟩, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← h5 _ ((mulVec_mem_perpX h1 _ _).1 (by rwa [e, h3])), e]
  · rw [← h6 _ ((mulVec_mem_perpX h1 _ _).1 (by rwa [e, h4])), e]
end IsoRig
end GlobalTheory.SgGlob
