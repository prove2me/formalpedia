-- Prove2me | solution 1 for Kyprianou.Ch02.levyGridLaplaceDeficitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:19:16.848721+00:00
-- url     : https://prove2.me/submissions/46b1772a-670a-4633-b4a2-fd7b3d19619e

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ q n ^ (n+1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ((n : ℝ)+1)*(1-q n) ≤ C := by
  obtain ⟨c,hc,h⟩ := h
  have hc1 : c ≤ 1 := by simpa using (h 0).trans (by simpa using (hq 0).2)
  refine ⟨-Real.log c, by linarith [Real.log_nonpos hc.le hc1], ?_⟩
  intro n
  have hp : 0 < q n := by
    by_contra hn
    have he : q n = 0 := le_antisymm (le_of_not_gt hn) (hq n).1
    have hh := h n
    simp [he] at hh
    linarith
  have hl := Real.log_le_log hc (h n)
  rw [Real.log_pow] at hl
  have hm := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp)
    (show 0 ≤ (n : ℝ) + 1 by positivity)
  push_cast at hl
  linarith
