-- Prove2me | solution 1 for Kyprianou.Ch01.cosineEndpointDivTendstoZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:11:17.578336+00:00
-- url     : https://prove2.me/submissions/a2e88ea8-5b58-4cee-a317-f35a040a1a76

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

/-- The bounded cosine correction in Dirichlet integration by parts vanishes. -/
theorem solution :
    Tendsto (fun R : ℝ => (1 - Real.cos R) / R) atTop (𝓝 0) := by
  have hcos : ∀ R : ℝ, 0 ≤ 1 - Real.cos R ∧ 1 - Real.cos R ≤ 2 := by
    intro R
    constructor
    · linarith [Real.cos_le_one R]
    · linarith [Real.neg_one_le_cos R]
  have hbound :
      ∀ R : ℝ, ‖(1 - Real.cos R) / R‖ ≤ 2 / |R| := by
    intro R
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hcos R).1]
    exact div_le_div_of_nonneg_right (hcos R).2 (abs_nonneg R)
  have hlim : Tendsto (fun R : ℝ => 2 / |R|) atTop (𝓝 0) := by
    have hinv : Tendsto (fun R : ℝ => 2 / R) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 : ℝ)
      simpa [div_eq_mul_inv] using h
    have heq :
        (fun R : ℝ => 2 / |R|) =ᶠ[atTop] (fun R : ℝ => 2 / R) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      simp only [abs_of_pos hR]
    exact hinv.congr' heq.symm
  exact squeeze_zero_norm hbound hlim
