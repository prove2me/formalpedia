-- Prove2me | solution 1 for GlobalTheory.HeckeLat.one_le_norm_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:25.965167+00:00
-- url     : https://prove2.me/submissions/82708cbc-9237-426f-aa07-51b0c70a995e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
import Theorems.Thm_GlobalTheory_HeckeLat_exists_one_le_norm
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeLat
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckeLat
theorem _root_.solution {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K}
    (hα : GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0) : 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  have h0 : α ≠ 0 := by
    rintro rfl
    apply hα
    funext i
    simp [GlobalTheory.HeckeTheta.emb]
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  exact hi.trans (norm_le_pi_norm (GlobalTheory.HeckeTheta.emb φ (α : K)) i)
end GlobalTheory.HeckeLat
