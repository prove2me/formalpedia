-- Prove2me | solution 1 for NarrowDNF.Weighted.exists_le_mean
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:58.796245+00:00
-- url     : https://prove2.me/submissions/90632196-150b-4db9-b3a5-bf3c82dfca7b

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
/-- A finite probability average has a realization at most its mean. Strictly
positive weights match the paper's interior Bernoulli biases. -/
theorem solution [Nonempty α] (weights : α → ℝ)
    (hw : ∀ x, 0 < weights x) (hs : ∑ x, weights x = 1) (value : α → ℝ) :
    ∃ x, value x ≤ ∑ y, weights y * value y := by
  classical
  by_contra h
  push_neg at h
  let m := ∑ y, weights y * value y
  have hlt : (∑ x, weights x * m) < ∑ x, weights x * value x := by
    apply Finset.sum_lt_sum
    · intro x _
      exact le_of_lt (mul_lt_mul_of_pos_left (h x) (hw x))
    · obtain ⟨x⟩ := ‹Nonempty α›
      exact ⟨x, Finset.mem_univ x, mul_lt_mul_of_pos_left (h x) (hw x)⟩
  have heq : (∑ x, weights x * m) = m := by rw [← Finset.sum_mul, hs, one_mul]
  rw [heq] at hlt
  exact (lt_irrefl m) hlt
