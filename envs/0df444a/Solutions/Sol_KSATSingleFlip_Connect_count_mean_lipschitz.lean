-- Prove2me | solution 1 for KSATSingleFlip.Connect.count_mean_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:42:28.972088+00:00
-- url     : https://prove2.me/submissions/8befa0c1-0102-45a4-bd08-8a2e7391a9c1

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem solution (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (g : ℕ → ℝ) (hg : Integrable g μ) (L r s : ℝ) (hL : 0 ≤ L)
    (hdev : Integrable (fun k : ℕ => |(k:ℝ)-r|) μ)
    (hmean : (∫ k : ℕ, |(k:ℝ)-r| ∂μ) ≤ s)
    (hlip : ∀ j k, |g j-g k| ≤ L*|(j:ℝ)-(k:ℝ)|) (j : ℕ) :
    |g j - ∫ k, g k ∂μ| ≤ L*(|(j:ℝ)-r|+s) := by
  have hp (k : ℕ) : |g j-g k| ≤ L*(|(j:ℝ)-r|+|(k:ℝ)-r|) := by
    calc
      |g j-g k| ≤ L*|(j:ℝ)-(k:ℝ)| := hlip j k
      _ ≤ L*(|(j:ℝ)-r|+|(k:ℝ)-r|) := by
        apply mul_le_mul_of_nonneg_left _ hL
        have h := abs_sub_le (j:ℝ) r (k:ℝ)
        simpa only [abs_sub_comm r (k:ℝ)] using h
  have hgi : Integrable (fun k => g j-g k) μ := (integrable_const (g j)).sub hg
  have hbound : Integrable (fun k : ℕ => L*(|(j:ℝ)-r|+|(k:ℝ)-r|)) μ :=
    ((integrable_const |(j:ℝ)-r|).add hdev).const_mul L
  have hident : |g j - ∫ k, g k ∂μ| = |∫ k, (g j - g k) ∂μ| := by
    rw [integral_sub (integrable_const (g j)) hg]
    simp
  rw [hident]
  calc
    |∫ k, (g j-g k) ∂μ| ≤ ∫ k, |g j-g k| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun k => g j-g k)
    _ ≤ ∫ k, L*(|(j:ℝ)-r|+|(k:ℝ)-r|) ∂μ := integral_mono hgi.abs hbound hp
    _ = L*(|(j:ℝ)-r| + ∫ k, |(k:ℝ)-r| ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const |(j:ℝ)-r|) hdev]
      simp
    _ ≤ L*(|(j:ℝ)-r|+s) := by gcongr
