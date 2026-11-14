-- Prove2me | solution 1 for NarrowDNF.Weighted.integer_markov
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:16:02.594628+00:00
-- url     : https://prove2.me/submissions/0559d494-fa57-4f1d-9f26-2857672a11eb

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Weighted
end NarrowDNF.Weighted


open NarrowDNF
open NarrowDNF
open NarrowDNF.Weighted
open scoped BigOperators
variable {α : Type*} [Fintype α]
/-- Integer-threshold Markov inequality for arbitrary finite nonnegative weights.
No probability normalization is needed for this inequality. -/
theorem solution (weights : α → ℝ) (hw : ∀ x, 0 ≤ weights x)
    (size : α → ℕ) (cutoff : ℕ) :
    (∑ x, weights x * (if cutoff < size x then 1 else 0)) ≤
      (∑ x, weights x * (size x : ℝ)) / (cutoff + 1 : ℝ) := by
  have hd : (0 : ℝ) < cutoff + 1 := by positivity
  apply (le_div_iff₀ hd).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : cutoff < size x
  · simp only [if_pos h, mul_one]
    have hs : (cutoff : ℝ) + 1 ≤ size x := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_left hs (hw x)
  · simp only [if_neg h, mul_zero, zero_mul]
    exact mul_nonneg (hw x) (Nat.cast_nonneg _)
