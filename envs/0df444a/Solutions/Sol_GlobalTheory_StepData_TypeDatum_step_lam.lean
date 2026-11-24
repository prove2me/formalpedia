-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.step_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:53:28.350845+00:00
-- url     : https://prove2.me/submissions/80259c7c-098e-4d99-9743-b5a2d525a5f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock

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
    (hg : (g : GL a k).val = (h : GL (a ⊕ t) k).val.toBlocks₁₁) :
    (P.step t μ hμ).lam h = P.lam g * (μ (Matrix.GeneralLinearGroup.det (g : GL a k)))⁻¹ *
      μ (Matrix.GeneralLinearGroup.det (h : GL (a ⊕ t) k)) := by
  obtain rfl : g = P.corner h := Subtype.ext (Units.ext (hg.trans (P.corner_val h).symm))
  rfl
end GlobalTheory.StepData.TypeDatum
