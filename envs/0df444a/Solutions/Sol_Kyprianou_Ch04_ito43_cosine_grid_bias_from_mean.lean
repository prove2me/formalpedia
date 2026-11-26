-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_grid_bias_from_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:47:23.586564+00:00
-- url     : https://prove2.me/submissions/9a341292-3e73-4b23-947b-aeec3b75dde7

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (T : NNReal) (c μ : ℝ) (n j : ℕ) (hn : 0 < n) (hj : j ≤ n)
    (t : NNReal) (e : ℝ) (he : 0 < e)
    (hmean : |(n:ℝ)*μ-c*(T:ℝ)| < e)
    (hclock : |(t:ℝ)-(T:ℝ)*(j:ℝ)/(n:ℝ)| ≤ (T:ℝ)/(n:ℝ)) :
    |c*(t:ℝ)-(j:ℝ)*μ| ≤ e+|c| * ((T:ℝ)/(n:ℝ)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hjR : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hj
  have hr0 : 0 ≤ (j:ℝ)/(n:ℝ) := by positivity
  have hr1 : (j:ℝ)/(n:ℝ) ≤ 1 := (div_le_one hnR).mpr hjR
  have heq : c*(t:ℝ)-(j:ℝ)*μ =
      c*((t:ℝ)-(T:ℝ)*(j:ℝ)/(n:ℝ)) +
        ((j:ℝ)/(n:ℝ))*(c*(T:ℝ)-(n:ℝ)*μ) := by
    field_simp
    <;> ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg hr0,abs_sub_comm (c*(T:ℝ))]
  have h1 := mul_le_mul_of_nonneg_left hclock (abs_nonneg c)
  have h2 := mul_le_mul_of_nonneg_right hr1 (abs_nonneg ((n:ℝ)*μ-c*(T:ℝ)))
  linarith
