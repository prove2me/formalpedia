-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.step_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:20.325006+00:00
-- url     : https://prove2.me/submissions/e9c9eaa3-afd6-4dc6-aee7-0d495aa788b9

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
theorem _root_.solution (μ : kˣ →* ℂˣ) (hμ : IsTame μ) : (P.step t μ hμ).J = P.stepJ t := rfl
end GlobalTheory.StepData.TypeDatum
