-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.rowE_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:04:46.831621+00:00
-- url     : https://prove2.me/submissions/d89a19eb-6da0-4d1c-b766-b10985e814f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.Model
theorem _root_.solution (l : Fin c) (u : n → k) (hu : u ≠ 0) : rowE c (l.val + 1) u ∉ N k n c (l.val + 1) := by
  rw [mem_N_iff]
  intro h
  apply hu
  funext s
  simpa [rowE, lowU] using h (Sum.inr l) (Sum.inl s) (by simp [lev])
end GlobalTheory.RootEx.Model
