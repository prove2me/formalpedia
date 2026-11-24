-- Prove2me | solution 1 for GlobalTheory.StepData.parahoric_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:47.808349+00:00
-- url     : https://prove2.me/submissions/d87b988e-7ab6-4f2f-9d3e-969a36362521

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_lam_eq

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
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
namespace GlobalTheory.StepData
theorem _root_.solution {δ : kˣ →* ℂˣ} {hδ : IsTame δ} (h : (parahoric r s δ hδ).J) (D : GL s k)
    (hD : D.val = (h : GL (r ⊕ s) k).val.toBlocks₂₂) :
    (parahoric r s δ hδ).lam h = δ (Matrix.GeneralLinearGroup.det D) := by
  have := (TypeDatum.full k r).step_lam_eq δ hδ h _ (TypeDatum.corner_val _ h) D hD
  exact this.trans (one_mul _)
end GlobalTheory.StepData
