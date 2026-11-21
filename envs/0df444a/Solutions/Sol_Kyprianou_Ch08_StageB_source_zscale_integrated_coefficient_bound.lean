-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_zscale_integrated_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:31:03.246272+00:00
-- url     : https://prove2.me/submissions/9cbdf506-c0ea-4ebf-8729-e7ab8da220cd

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_scaleConvolutionPower_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_scaleConvolutionPower_factorial_majorant
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB Set

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (hconv : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ =>
        W 0 s * scaleConvolutionPower (W 0) n (x - s))
        (Set.Ioc (0 : ℝ) x) volume)
    (x : ℝ) (hx : 0 < x) :
    ∀ n : ℕ,
      ‖(((∫ y in (0 : ℝ)..x,
        scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)‖ ≤
      (x * W 0 x) * (x * W 0 x) ^ n / (Nat.factorial n : ℝ) := by
  intro n
  rcases source_family_positive_monotone ψ W hW 0 (le_refl (0 : ℝ)) with
    ⟨hpos, hmono, _⟩
  have hfac : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  let C : ℝ := (x ^ n / (Nat.factorial n : ℝ)) * W 0 x ^ (n + 1)
  have hb : ∀ y ∈ Set.uIoc (0 : ℝ) x,
      ‖scaleConvolutionPower (W 0) n y‖ ≤ C := by
    intro y hy
    have hy' : y ∈ Set.Ioc (0 : ℝ) x := by
      simpa [Set.uIoc_of_le hx.le] using hy
    have hfy : 0 ≤ scaleConvolutionPower (W 0) n y :=
      scaleConvolutionPower_nonnegative (W 0)
        (fun t _ => hpos t) n y hy'.1.le
    have hmajor := scaleConvolutionPower_factorial_majorant
      (W 0) (fun t _ => hpos t) hmono hconv n y hy'.1.le
    have hpow : y ^ n ≤ x ^ n := by
      gcongr
      · exact hy'.1.le
      · exact hy'.2
    have hWpow : W 0 y ^ (n + 1) ≤ W 0 x ^ (n + 1) := by
      gcongr
      · exact hpos y
      · exact hmono hy'.1.le hx.le hy'.2
    have hcoef : y ^ n / (Nat.factorial n : ℝ) ≤
        x ^ n / (Nat.factorial n : ℝ) :=
      div_le_div_of_nonneg_right hpow hfac.le
    have hcoefnonneg : 0 ≤ x ^ n / (Nat.factorial n : ℝ) := by positivity
    have hpow_nonneg : 0 ≤ W 0 y ^ (n + 1) :=
      pow_nonneg (hpos y) _
    calc
      ‖scaleConvolutionPower (W 0) n y‖ =
          scaleConvolutionPower (W 0) n y := by
        simp only [Real.norm_eq_abs, abs_of_nonneg hfy]
      _ ≤ (y ^ n / (Nat.factorial n : ℝ)) * W 0 y ^ (n + 1) := hmajor
      _ ≤ (x ^ n / (Nat.factorial n : ℝ)) * W 0 y ^ (n + 1) :=
        mul_le_mul_of_nonneg_right hcoef hpow_nonneg
      _ ≤ C := mul_le_mul_of_nonneg_left hWpow hcoefnonneg
  have hbound : ‖(∫ y in (0 : ℝ)..x,
      scaleConvolutionPower (W 0) n y)‖ ≤ C * |x - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc
    ‖(((∫ y in (0 : ℝ)..x,
      scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)‖ =
        ‖(∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y)‖ :=
      Complex.norm_real _
    _ ≤ C * |x - 0| := hbound
    _ = (x * W 0 x) * (x * W 0 x) ^ n /
          (Nat.factorial n : ℝ) := by
      dsimp [C]
      simp only [sub_zero, abs_of_pos hx]
      rw [mul_pow]
      ring
