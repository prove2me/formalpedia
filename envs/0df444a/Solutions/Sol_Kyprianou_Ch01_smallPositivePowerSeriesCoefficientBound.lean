-- Prove2me | solution 1 for Kyprianou.Ch01.smallPositivePowerSeriesCoefficientBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:34:47.634795+00:00
-- url     : https://prove2.me/submissions/22e4fb10-e3a2-42eb-a1ce-45052e758621

import Mathlib

import Theorems.Thm_Kyprianou_Ch01_smallPositivePowerSeriesTailHasSum
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
theorem solution
    (a : ℕ → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i : ℕ, |a i| ≤ M)
    (h : ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
        HasSum (fun n : ℕ => z ^ n * a n) 0)
    (k : ℕ) (hprefix : ∀ i : ℕ, i < k → a i = 0)
    (z : ℝ) (hz : 0 < z) (hz2 : z ≤ (1/2 : ℝ)) :
    |a k| ≤ 2 * M * z := by
  have h2 :=
    Kyprianou.Ch01.smallPositivePowerSeriesTailHasSum
      a h k hprefix z hz hz2
  have hg : HasSum (fun i : ℕ => z ^ (i+1) * M) (z * M / (1 - z)) := by
    have := (hasSum_geometric_of_lt_one hz.le (by linarith)).mul_left (z * M)
    have e1 : (fun i : ℕ => z ^ (i+1) * M) = fun i => z * M * z ^ i := by
      funext i; ring
    have hz1 : (1 - z) ≠ 0 := by linarith
    have e2 : z * M / (1 - z) = z * M * (1 - z)⁻¹ := by rw [div_eq_mul_inv]
    rw [e1, e2]; exact this
  have hb : ∀ i, |z ^ (i+1) * a (i + (k+1))| ≤ z ^ (i+1) * M := by
    intro i
    rw [abs_mul, abs_of_pos (pow_pos hz _)]
    exact mul_le_mul_of_nonneg_left (hM _) (pow_pos hz _).le
  have u1 : -(a k) ≤ z * M / (1 - z) := hasSum_le (fun i => (abs_le.mp (hb i)).2) h2 hg
  have u2 : -(z * M / (1 - z)) ≤ -(a k) :=
    hasSum_le (fun i => by simpa using (abs_le.mp (hb i)).1) hg.neg h2
  have hzM : z * M / (1 - z) ≤ 2 * M * z := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg (mul_nonneg hz.le hM0) (by linarith : (0:ℝ) ≤ 1/2 - z)]
  rw [abs_le]; constructor <;> linarith
