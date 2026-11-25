-- Prove2me | solution 1 for GlobalTheory.BasicFlow.truncate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:40.440802+00:00
-- url     : https://prove2.me/submissions/bb761e87-6799-401f-a0f3-d83e24695b17

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.BasicFlow
namespace GlobalTheory.BasicFlow
theorem _root_.solution (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (i0 : ℕ)
    (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d W x) :
    ∃ x' : ZMod d → ℕ → ℝ, IsFlow l d W x' ∧
      (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x' a i = 0) ∧
      flowVal d x ≤ flowVal d x' + (∑ a, W a) / (l : ℝ) ^ i0 := by
  obtain ⟨h0, h2⟩ := hx
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  let y : ZMod d → ℕ → ℝ := fun a i => if i0 ≤ i ∨ i ∉ oddLevels d then 0 else x a i
  have hy : ∀ a i, y a i ≤ x a i := fun a i => by
    simp only [y]; split_ifs
    · exact h0 a i
    · exact le_rfl
  refine ⟨y, ⟨fun a i => ?_, fun a => le_trans (add_le_add ?_ ?_) (h2 a)⟩,
    fun a i h => if_pos h, ?_⟩
  · simp only [y]; split_ifs
    · exact le_rfl
    · exact h0 a i
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy a i) (by positivity)
  · exact Finset.sum_le_sum fun i _ => hy _ i
  · have hp : (0 : ℝ) < (l : ℝ) ^ i0 := by positivity
    rw [← sub_le_iff_le_add', le_div_iff₀ hp]
    unfold flowVal
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    have e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
    have e3 : (∑ i ∈ oddLevels d, x a i - ∑ i ∈ oddLevels d, y a i) * (l : ℝ) ^ i0
        ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases h : i0 ≤ i
      · have : y a i = 0 := if_pos (Or.inl h)
        rw [this, sub_zero, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 h) (h0 a i)
      · have : y a i = x a i := if_neg (by simp [h, hi])
        rw [this, sub_self, zero_mul]
        exact mul_nonneg (by positivity) (h0 a i)
    have := h2 a
    linarith
end GlobalTheory.BasicFlow
