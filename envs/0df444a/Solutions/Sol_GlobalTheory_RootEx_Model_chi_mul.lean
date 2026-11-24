-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:14.649289+00:00
-- url     : https://prove2.me/submissions/57256226-f82b-407f-a17f-721630bd63a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Theorems.Thm_GlobalTheory_RootEx_Model_simpleSum_mul

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
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.Model
theorem _root_.solution (ψ : AddChar k Circle) (p : ℕ) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (h) :
    chi ψ p (u * h) = (ψ (simpleSum u) : ℂ) * chi ψ p h := by
  unfold chi
  by_cases hh : h ∈ N k n c p
  · rw [if_pos hh, if_pos (mul_mem hu hh), simpleSum_mul hu hh, AddChar.map_add_eq_mul]; simp
  · rw [if_neg hh, if_neg (by rwa [Subgroup.mul_mem_cancel_left _ hu]), mul_zero]
end GlobalTheory.RootEx.Model
