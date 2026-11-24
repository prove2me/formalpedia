-- Prove2me | solution 1 for GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:45.933431+00:00
-- url     : https://prove2.me/submissions/541a39d3-38c7-49ad-bc28-772db5d68b77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormula
import Theorems.Thm_GlobalTheory_SliceOpDeriv_hasFDerivAt_sliceR_apply
import Theorems.Thm_GlobalTheory_SliceOpDeriv_continuous_xPart
import Theorems.Thm_GlobalTheory_SliceOpDeriv_continuous_yPart

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
open GlobalTheory GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
namespace GlobalTheory.SliceOpDeriv
theorem _root_.solution (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V) :
    HasFDerivAt (qOp P f)
      (((xPart P f (s ∘ Sum.inl) (s ∘ Sum.inr)).coprod
        (fderiv ℝ (P (sliceR f (s ∘ Sum.inl))) (s ∘ Sum.inr))).comp splitL) s := by
  let F : (κ → V) → (κ₁' → V) → ℂ := fun x y => P (sliceR f x) y
  have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := splitL s) (f := F)
    (f₁ := fun x y => xPart P f x y) (f₂ := fun x y => fderiv ℝ (P (sliceR f x)) y)
    (Filter.Eventually.of_forall fun v => hasFDerivAt_sliceR_apply P f v.1 v.2)
    (Filter.Eventually.of_forall fun v => ((P (sliceR f v.1)).differentiableAt).hasFDerivAt)
    (continuous_xPart P f).continuousAt (continuous_yPart P f).continuousAt
  have h2 := key.hasFDerivAt.comp s ((splitL (V := V) (κ := κ) (κ₁' := κ₁')).hasFDerivAt (x := s))
  exact h2
end GlobalTheory.SliceOpDeriv
