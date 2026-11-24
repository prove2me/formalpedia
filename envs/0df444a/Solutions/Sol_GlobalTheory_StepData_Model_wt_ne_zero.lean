-- Prove2me | solution 1 for GlobalTheory.StepData.Model.wt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:02:55.409743+00:00
-- url     : https://prove2.me/submissions/583c3cf5-2033-439b-8f49-59d8401c1968

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero

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
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n]
namespace GlobalTheory.StepData.Model
theorem _root_.solution (ϖ : kˣ) (i : n ⊕ Fin c) : wt ϖ i ≠ 0 := by
  rcases i with i | i <;> simp [wt]
end GlobalTheory.StepData.Model
