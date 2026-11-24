-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.step_lam_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:19.914488+00:00
-- url     : https://prove2.me/submissions/1f16565c-fd2c-4eb5-9e95-d492348da007

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_lam
import Theorems.Thm_GlobalTheory_StepData_tame_det_blocks


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
open GlobalTheory.StepData.TypeDatum
variable (P : TypeDatum k a)
namespace GlobalTheory.StepData.TypeDatum
theorem _root_.solution (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (h : P.stepJ t) (g : P.J)
    (hg : (g : GL a k).val = (h : GL (a ⊕ t) k).val.toBlocks₁₁) (D : GL t k)
    (hD : D.val = (h : GL (a ⊕ t) k).val.toBlocks₂₂) :
    (P.step t μ hμ).lam h = P.lam g * μ (Matrix.GeneralLinearGroup.det D) := by
  rw [P.step_lam μ hμ h g hg, tame_det_blocks hμ h.2.1 h.2.2.2.2.1 hg hD, mul_assoc, inv_mul_cancel_left]
end GlobalTheory.StepData.TypeDatum
