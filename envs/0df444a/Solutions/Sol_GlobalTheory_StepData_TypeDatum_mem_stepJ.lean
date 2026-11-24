-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.mem_stepJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:00.795548+00:00
-- url     : https://prove2.me/submissions/7f43b9f5-98a5-4d56-a74c-0a23fba7be2e

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
theorem _root_.solution {h : GL (a ⊕ t) k} : h ∈ P.stepJ t ↔ h ∈ KO k (a ⊕ t) ∧ (∃ g ∈ P.J, g.val = h.val.toBlocks₁₁) ∧
    IntM h.val.toBlocks₁₂ ∧ MaxM h.val.toBlocks₂₁ ∧ ∃ D ∈ KO k t, D.val = h.val.toBlocks₂₂ := Iff.rfl
end GlobalTheory.StepData.TypeDatum
