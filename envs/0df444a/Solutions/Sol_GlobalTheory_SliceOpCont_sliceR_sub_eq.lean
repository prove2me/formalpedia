-- Prove2me | solution 1 for GlobalTheory.SliceOpCont.sliceR_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:06.889833+00:00
-- url     : https://prove2.me/submissions/6b651fde-d2b6-4fb0-96d6-fbc6a9e9ef78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOpCont
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceOpCont
theorem _root_.solution {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x x₀ : κ → V) :
    sliceR f x - sliceR f x₀
      = sliceR (SchwartzMap.compSubConstCLM ℂ (-(padL (κ' := κ') (x - x₀))) f - f) x₀ := by
  ext y
  have he : (Sum.elim x₀ y : κ ⊕ κ' → V) + padL (x - x₀) = Sum.elim x y := by
    funext i
    cases i with
    | inl i => simp [padL]
    | inr j => simp [padL]
  simp [SchwartzMap.compSubConstCLM_apply, he]
end GlobalTheory.SliceOpCont
