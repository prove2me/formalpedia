-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.colE_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:39.408869+00:00
-- url     : https://prove2.me/submissions/161f32f8-17cc-40ba-827e-e0938e914c75

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
theorem _root_.solution (p : ℕ) (β : n → k) : colE c (p + 1) β ∈ N k n c p := by
  rw [mem_N_iff]
  rintro (r | r) (s | s) h <;> simp [colE, upU, lev, Matrix.one_apply] at h ⊢
  omega
end GlobalTheory.RootEx.Model
