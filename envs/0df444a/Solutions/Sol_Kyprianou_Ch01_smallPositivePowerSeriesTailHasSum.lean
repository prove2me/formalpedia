-- Prove2me | solution 1 for Kyprianou.Ch01.smallPositivePowerSeriesTailHasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:34:40.354011+00:00
-- url     : https://prove2.me/submissions/77619ee8-f4ff-4da5-9d82-4f55f5d3d9f6

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
set_option autoImplicit false

theorem solution
    (a : ℕ → ℝ)
    (h : ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
        HasSum (fun n : ℕ => z ^ n * a n) 0)
    (k : ℕ) (hprefix : ∀ i : ℕ, i < k → a i = 0)
    (z : ℝ) (hz : 0 < z) (hz2 : z ≤ (1/2 : ℝ)) :
    HasSum (fun i : ℕ => z ^ (i + 1) * a (i + (k + 1))) (-(a k)) := by
  have hs := h z hz hz2
  have h1 := (hasSum_nat_add_iff' (k+1)).mpr hs
  have hfin : ∑ i ∈ Finset.range (k+1), z ^ i * a i = z ^ k * a k := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
      rw [hprefix i (Finset.mem_range.mp hi), mul_zero]), zero_add]
  rw [hfin] at h1
  have hzk : 0 < z ^ k := pow_pos hz k
  have h2 : HasSum (fun i => z ^ (i+1) * a (i + (k+1))) (-(a k)) := by
    have := h1.mul_left (1 / z ^ k)
    have e1 : (fun i => z ^ (i+1) * a (i + (k+1))) =
        fun i => 1 / z ^ k * (z ^ (i + (k + 1)) * a (i + (k + 1))) := by
      funext i; rw [pow_add, pow_succ]; field_simp; ring
    have e2 : -(a k) = 1 / z ^ k * (0 - z ^ k * a k) := by rw [zero_sub]; field_simp
    rw [e1, e2]; exact this
  exact h2