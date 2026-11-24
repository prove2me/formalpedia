-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.rowAt_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:34.796086+00:00
-- url     : https://prove2.me/submissions/9fd06eb4-4be0-4e34-8758-5a1d1298a6be

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
theorem _root_.solution (x₀ : Matrix n n' k) (e) (u : n' → k) (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) :
    rowAt n c p u r s = 0 ∨ affPt (c := c) p x₀ e r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · left; simp [rowAt]
  · left; simp [rowAt]
  · by_cases h : r.val + 1 = p
    · right
      subst h
      simp [affPt, basePt, Free]
    · left; simp [rowAt, h]
  · left; simp [rowAt]
end GlobalTheory.LocFlat.UnramFlat
