-- Prove2me | solution 1 for GlobalTheory.PosEntries.exists_affPt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:16:17.279523+00:00
-- url     : https://prove2.me/submissions/46a39423-fd29-42bb-b7b9-a74295475007

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.PosEntries
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.PosEntries
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k} (h : opE ψ ν p Ψ x₀ ≠ 0) :
    ∃ e, Ψ (affPt p x₀ e) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  simp [opE, hn]
end GlobalTheory.PosEntries
