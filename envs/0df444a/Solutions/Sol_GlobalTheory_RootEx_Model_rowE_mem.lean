-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.rowE_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:32.077023+00:00
-- url     : https://prove2.me/submissions/8c973682-a41b-48bc-8c5c-aed4d9c2ff3f

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
theorem _root_.solution (p : ℕ) (u : n → k) : rowE c p u ∈ N k n c (p + 1) := by
  rw [mem_N_iff]
  rintro (r | r) (s | s) h <;> simp [rowE, lowU, lev, Matrix.one_apply] at h ⊢
  omega
end GlobalTheory.RootEx.Model
