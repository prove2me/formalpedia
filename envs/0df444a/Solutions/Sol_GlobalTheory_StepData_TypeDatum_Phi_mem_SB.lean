-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.Phi_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:47.764336+00:00
-- url     : https://prove2.me/submissions/67ddafb4-58f9-4ef1-a2cd-8b6425a4c56b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_add
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_intM_of_Phi_ne_zero
import Theorems.Thm_GlobalTheory_StepData_mem_SB_of_periodic

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
omit [DecidableEq t]
namespace GlobalTheory.StepData
namespace TypeDatum
theorem _root_.solution (P : TypeDatum k a) {μ : kˣ →* ℂˣ} (hμ : IsTame μ) :
    P.Phi t μ ∈ SB (Matrix (a ⊕ t) a k) :=
  mem_SB_of_periodic (fun _ => P.intM_of_Phi_ne_zero μ) fun x _ hy => P.Phi_add hμ x hy
end TypeDatum
end GlobalTheory.StepData
