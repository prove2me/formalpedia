-- Prove2me | solution 1 for GlobalTheory.SgGlob.IsoRig.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:11.057033+00:00
-- url     : https://prove2.me/submissions/8ea7b359-f4e0-45b2-8522-fa1c360087da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_mulVec_mem_perpX
import Theorems.Thm_GlobalTheory_SgGlob_isUn_mul
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
theorem _root_.solution {γ δ : Matrix (Fin n) (Fin n) E} {c d e : Rig E n m r} (h : IsoRig σ J γ c d)
    (k : IsoRig σ J δ d e) : IsoRig σ J (δ * γ) c e := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
  obtain ⟨⟨k1, k2, k3, k4⟩, k5, k6⟩ := k
  refine ⟨⟨isUn_mul k1 h1, by rw [latMap_mul, h2, k2], by rw [Matrix.mul_assoc, h3, k3],
    by rw [Matrix.mul_assoc, h4, k4]⟩, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← Matrix.mulVec_mulVec, k5 _ (h3 ▸ (mulVec_mem_perpX h1 _ v).2 hv), h5 v hv]
  · rw [← Matrix.mulVec_mulVec, k6 _ (h4 ▸ (mulVec_mem_perpX h1 _ v).2 hv), h6 v hv]
end IsoRig
end GlobalTheory.SgGlob
