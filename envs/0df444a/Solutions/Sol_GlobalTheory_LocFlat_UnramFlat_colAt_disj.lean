-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.colAt_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:29:14.42155+00:00
-- url     : https://prove2.me/submissions/d565283b-968a-413d-b55e-11f0b67e3513

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
theorem _root_.solution (x₀ : Matrix n n' k) (e) (y : n → k) (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) :
    colAt n' c p y r s = 0 ∨ affPt (c := c) p x₀ e r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · left; simp [colAt]
  · by_cases h : s.val + 1 = p
    · right
      subst h
      simp [affPt, basePt, Free]
    · left; simp [colAt, h]
  · left; simp [colAt]
  · left; simp [colAt]
end GlobalTheory.LocFlat.UnramFlat
