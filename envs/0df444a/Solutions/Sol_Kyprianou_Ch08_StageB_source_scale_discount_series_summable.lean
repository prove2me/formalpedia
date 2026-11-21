-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_discount_series_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:32:00.509202+00:00
-- url     : https://prove2.me/submissions/87574730-94c2-45d5-9d5a-19bc31045a4c

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_coeff_majorant
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (hconv : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ =>
        W 0 s * scaleConvolutionPower (W 0) n (x - s))
        (Set.Ioc (0 : ℝ) x) volume)
    (x q : ℝ) (hx : 0 ≤ x) (hq : 0 ≤ q) :
    Summable (fun n : ℕ =>
      q ^ n * scaleConvolutionPower (W 0) n x) := by
  have hM : 0 ≤ W 0 x :=
    (source_family_positive_monotone ψ W hW 0 (le_refl (0 : ℝ))).1 x
  let R : ℝ := x * W 0 x
  have hcoef := source_scale_convolution_coeff_majorant ψ W hW hconv x hx
  have hs : Summable (fun n : ℕ =>
      W 0 x * (q * R) ^ n / (Nat.factorial n : ℝ)) := by
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial (q * R)).mul_left (W 0 x)
  apply Summable.of_norm_bounded hs
  intro n
  have hc : ‖scaleConvolutionPower (W 0) n x‖ ≤
      W 0 x * R ^ n / (Nat.factorial n : ℝ) := by
    simpa only [Complex.norm_real] using hcoef n
  calc
    ‖q ^ n * scaleConvolutionPower (W 0) n x‖ =
        q ^ n * ‖scaleConvolutionPower (W 0) n x‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq n)]
    _ ≤ q ^ n * (W 0 x * R ^ n / (Nat.factorial n : ℝ)) :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg hq n)
    _ = W 0 x * (q * R) ^ n / (Nat.factorial n : ℝ) := by
      rw [mul_pow]
      ring
