-- Prove2me | solution 1 for GlobalTheory.SliceOp.continuous_qOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:36.840223+00:00
-- url     : https://prove2.me/submissions/52ca3795-8ca8-4367-8a7e-2f1241fbcc3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Theorems.Thm_GlobalTheory_SliceOpCont_continuous_sliceR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory.SliceOpCont
namespace GlobalTheory.SliceOp
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (qOp P f) := by
  have hinl : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inl) := by fun_prop
  have hinr : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inr) := by fun_prop
  have hG : Continuous (fun s : κ ⊕ κ₁' → V =>
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ (P (sliceR f (s ∘ Sum.inl)))) :=
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ).continuous.comp
      (P.continuous.comp ((continuous_sliceR V f).comp hinl))
  have hq : qOp P f = fun s => (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ
      (P (sliceR f (s ∘ Sum.inl)))) (s ∘ Sum.inr) := by
    funext s; rfl
  rw [hq]
  exact continuous_eval.comp (hG.prodMk hinr)
end GlobalTheory.SliceOp
