-- Prove2me | solution 1 for Kyprianou.Ch01.pmfLaplace_argumentLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:44:04.214453+00:00
-- url     : https://prove2.me/submissions/ec315bf0-943f-4629-ba25-68d371992c56

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_pmfLaplace_summable
import Theorems.Thm_Kyprianou_Ch01_exp_uniform_lipschitz_on_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Uniform moment-free continuity of the offspring PMF Laplace transform. -/
theorem solution (p : PMF ℕ) (delta : ℝ) (hd : 0 < delta)
    (x y : ℝ) (hx : delta ≤ x) (hy : delta ≤ y) :
    |(∑' k : ℕ, (p k).toReal * Real.exp (-y * (k : ℝ))) -
      (∑' k : ℕ, (p k).toReal * Real.exp (-x * (k : ℝ)))| ≤
      delta⁻¹ * |y - x| := by
  have hx0 : 0 ≤ x := le_trans (le_of_lt hd) hx
  have hy0 : 0 ≤ y := le_trans (le_of_lt hd) hy
  have hsx := Kyprianou.Ch01.pmfLaplace_summable p x hx0
  have hsy := Kyprianou.Ch01.pmfLaplace_summable p y hy0
  have hp : Summable (fun k : ℕ => (p k).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hmass : (∑' k : ℕ, (p k).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq
      (ENNReal.ne_top_of_tsum_ne_top p.tsum_coe_ne_top), p.tsum_coe]
    norm_num
  have hdiff : Summable (fun k : ℕ =>
      (p k).toReal * (Real.exp (-y * (k : ℝ)) -
        Real.exp (-x * (k : ℝ)))) := by
    simpa only [mul_sub] using hsy.sub hsx
  have hmajor : Summable (fun k : ℕ =>
      (p k).toReal * (delta⁻¹ * |y - x|)) := hp.mul_right _
  calc
    _ = ‖∑' k : ℕ, (p k).toReal *
        (Real.exp (-y * (k : ℝ)) - Real.exp (-x * (k : ℝ)))‖ := by
      rw [Real.norm_eq_abs, ← hsy.tsum_sub hsx]
      simp only [mul_sub]
    _ ≤ ∑' k : ℕ, ‖(p k).toReal *
        (Real.exp (-y * (k : ℝ)) - Real.exp (-x * (k : ℝ)))‖ :=
      norm_tsum_le_tsum_norm hdiff.norm
    _ ≤ ∑' k : ℕ, (p k).toReal * (delta⁻¹ * |y - x|) := by
      apply hdiff.norm.tsum_le_tsum _ hmajor
      intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left
        (Kyprianou.Ch01.exp_uniform_lipschitz_on_positive delta hd k x y hx hy)
        ENNReal.toReal_nonneg
    _ = (∑' k : ℕ, (p k).toReal) * (delta⁻¹ * |y - x|) := by
      rw [tsum_mul_right]
    _ = delta⁻¹ * |y - x| := by rw [hmass, one_mul]
