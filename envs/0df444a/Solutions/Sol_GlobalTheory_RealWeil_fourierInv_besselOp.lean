-- Prove2me | solution 1 for GlobalTheory.RealWeil.fourierInv_besselOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:45.778259+00:00
-- url     : https://prove2.me/submissions/28ac3025-7438-4152-af3e-8bd1dc5d72f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_fourierInv_dRho_inl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (f : Sch l) : 𝓕⁻ (besselOp l f) = weightOp l (𝓕⁻ f) := by
  let F : Sch l →L[ℂ] Sch l := FourierTransform.fourierInvCLM ℂ (Sch l)
  have hF : ∀ g : Sch l, 𝓕⁻ g = F g := fun _ => rfl
  have h := fourierInv_dRho_inl (l := l)
  simp only [hF] at h ⊢
  simp only [besselOp, weightOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul,
    map_sum, h, map_neg, neg_neg]
end GlobalTheory.RealWeil
