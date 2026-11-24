-- Prove2me | solution 1 for GlobalTheory.StepData.Model.typeFrame_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:02:54.483034+00:00
-- url     : https://prove2.me/submissions/6b86a97e-c370-4644-85ca-f53f0cc61816

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData.Model
theorem _root_.solution (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) : (typeFrame ϖ o).bas.val = diagonal (wt ϖ) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← diagonal_one, fromBlocks_diagonal]; congr
end GlobalTheory.StepData.Model
