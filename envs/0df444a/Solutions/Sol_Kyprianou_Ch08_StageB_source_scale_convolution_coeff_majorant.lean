-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_convolution_coeff_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:11:26.348184+00:00
-- url     : https://prove2.me/submissions/6abf4549-f591-4711-9ed0-034664685ef0

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_scaleConvolutionPower_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_scaleConvolutionPower_factorial_majorant
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (hint : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ =>
        W 0 s * scaleConvolutionPower (W 0) n (x - s))
        (Set.Ioc (0 : ℝ) x) volume)
    (x : ℝ) (hx : 0 ≤ x) :
    ∀ n : ℕ,
      ‖((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)‖ ≤
        W 0 x * (x * W 0 x) ^ n / (Nat.factorial n : ℝ) := by
  intro n
  rcases source_family_positive_monotone ψ W hW 0 (le_refl (0 : ℝ)) with
    ⟨hpos, hmono, _⟩
  have hp := scaleConvolutionPower_nonnegative (W 0)
      (fun t ht => hpos t) n x hx
  have hmajor := scaleConvolutionPower_factorial_majorant
    (W 0) (fun t ht => hpos t) hmono hint n x hx
  calc
    ‖((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)‖ =
        scaleConvolutionPower (W 0) n x := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    _ ≤ (x ^ n / (Nat.factorial n : ℝ)) * (W 0 x) ^ (n + 1) := hmajor
    _ = W 0 x * (x * W 0 x) ^ n / (Nat.factorial n : ℝ) := by
      rw [mul_pow, pow_succ]
      ring
