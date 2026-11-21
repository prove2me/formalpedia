-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_compact_factorial_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:12:16.696441+00:00
-- url     : https://prove2.me/submissions/d0e62481-2b44-44dc-bac5-9036481c47a2

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_all_power_local_integrability
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_coeff_majorant
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q R : ℝ) (hq : 0 ≤ q) (hR : 0 ≤ R) :
    ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (0 : ℝ) R →
      ‖q ^ n * scaleConvolutionPower (W 0) n x‖ ≤
      W 0 R * (q * R * W 0 R) ^ n / (Nat.factorial n : ℝ) := by
  obtain ⟨hpos,hmono,_⟩ := source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))
  have hconv := source_scale_all_power_local_integrability ψ W hW
  intro n x hx
  have hcoeff := (source_scale_convolution_coeff_majorant ψ W hW hconv x hx.1) n
  have hfn : ‖scaleConvolutionPower (W 0) n x‖ ≤
      W 0 x * (x * W 0 x) ^ n / (Nat.factorial n : ℝ) := by
    simpa only [Complex.norm_real] using hcoeff
  have hw : W 0 x ≤ W 0 R :=
    hmono hx.1 hR hx.2
  have hWx : 0 ≤ W 0 x := hpos x
  have hWR : 0 ≤ W 0 R := hpos R
  have hxx : x * W 0 x ≤ R * W 0 R :=
    mul_le_mul hx.2 hw hWx hR
  have hnonneg : 0 ≤ x * W 0 x := mul_nonneg hx.1 hWx
  have hpow : (x * W 0 x) ^ n ≤ (R * W 0 R) ^ n := by
    exact pow_le_pow_left₀ hnonneg hxx _
  have hA : 0 ≤ (x * W 0 x) ^ n :=
    pow_nonneg (mul_nonneg hx.1 hWx) _
  have hB : 0 ≤ (R * W 0 R) ^ n :=
    pow_nonneg (mul_nonneg hR hWR) _
  have hmul : W 0 x * (x * W 0 x) ^ n ≤
      W 0 R * (R * W 0 R) ^ n :=
    mul_le_mul hw hpow hA hWR
  have hdiv : W 0 x * (x * W 0 x) ^ n / (Nat.factorial n : ℝ) ≤
      W 0 R * (R * W 0 R) ^ n / (Nat.factorial n : ℝ) :=
    div_le_div_of_nonneg_right hmul (by positivity)
  calc
    ‖q ^ n * scaleConvolutionPower (W 0) n x‖ =
        q ^ n * ‖scaleConvolutionPower (W 0) n x‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq n)]
    _ ≤ q ^ n * (W 0 x * (x * W 0 x) ^ n / (Nat.factorial n : ℝ)) :=
      mul_le_mul_of_nonneg_left hfn (pow_nonneg hq n)
    _ ≤ q ^ n * (W 0 R * (R * W 0 R) ^ n / (Nat.factorial n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (pow_nonneg hq _)
    _ = W 0 R * (q * R * W 0 R) ^ n / (Nat.factorial n : ℝ) := by
      rw [mul_pow]
      ring
