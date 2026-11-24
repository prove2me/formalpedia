-- Prove2me | solution 1 for GlobalTheory.StepData.parPhi_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:53:32.384965+00:00
-- url     : https://prove2.me/submissions/964e328d-ee93-4787-b2b7-ef47c8273d3b

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
variable {r s s' : Type*} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
omit [Fintype s] [DecidableEq s] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
theorem _root_.solution (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} :
    parPhi δ x ≠ 0 ↔ (∃ g ∈ KO k r, g.val = x.toBlocks₁₁) ∧ MaxM x.toBlocks₂₁ ∧ IntM x.toBlocks₁₂ ∧
      IntM x.toBlocks₂₂ := by
  unfold parPhi
  split_ifs with h <;> simp [h, extZ_ne_zero_iff]
end GlobalTheory.StepData
