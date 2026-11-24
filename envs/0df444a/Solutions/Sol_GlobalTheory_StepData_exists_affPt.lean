-- Prove2me | solution 1 for GlobalTheory.StepData.exists_affPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:22.423668+00:00
-- url     : https://prove2.me/submissions/4c804043-7eab-4d94-b9d3-9669813e1b1b

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
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n']
namespace GlobalTheory.StepData
theorem _root_.solution {p : ℕ} {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k}
    (h : ∀ r s, ¬ Free p (r, s) → x r s = basePt c x.toBlocks₁₁ r s) : ∃ e, affPt p x.toBlocks₁₁ e = x := by
  refine ⟨fun rs => x rs.1.1 rs.1.2 - basePt c x.toBlocks₁₁ rs.1.1 rs.1.2, ?_⟩
  ext r s
  by_cases hf : Free p (r, s) <;> simp [affPt, hf, h]
end GlobalTheory.StepData
