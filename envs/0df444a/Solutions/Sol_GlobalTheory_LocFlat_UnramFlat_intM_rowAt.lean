-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.intM_rowAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:32.572751+00:00
-- url     : https://prove2.me/submissions/0d61cf1a-834a-42d3-a752-ac99f1963cc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c p : ℕ}
namespace GlobalTheory.LocFlat.UnramFlat
theorem _root_.solution (u : n' → k) :
    IntM (rowAt (k := k) n c p u) ↔ ∀ l : Fin c, l.val + 1 = p → ∀ s, u s ∈ 𝒪[k] := by
  constructor
  · intro h l hl s
    simpa [rowAt, hl] using h (Sum.inr l) (Sum.inl s)
  · intro h r s
    rcases r with r | r <;> rcases s with s | s
    · simp [rowAt]
    · simp [rowAt]
    · simp only [rowAt, fromBlocks_apply₂₁, Matrix.of_apply]
      split_ifs with hs
      exacts [h r hs s, zero_mem _]
    · simp [rowAt]
end GlobalTheory.LocFlat.UnramFlat
