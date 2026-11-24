-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.intM_colAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:31.62159+00:00
-- url     : https://prove2.me/submissions/eca6b936-3a21-4b52-990f-bf651f565a88

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
theorem _root_.solution (y : n → k) :
    IntM (colAt (k := k) n' c p y) ↔ ∀ i : Fin (c + 1), i.val + 1 = p → ∀ r, y r ∈ 𝒪[k] := by
  constructor
  · intro h i hi r
    simpa [colAt, hi] using h (Sum.inl r) (Sum.inr i)
  · intro h r s
    rcases r with r | r <;> rcases s with s | s
    · simp [colAt]
    · simp only [colAt, fromBlocks_apply₁₂, Matrix.of_apply]
      split_ifs with hs
      exacts [h s hs r, zero_mem _]
    · simp [colAt]
    · simp [colAt]
end GlobalTheory.LocFlat.UnramFlat
