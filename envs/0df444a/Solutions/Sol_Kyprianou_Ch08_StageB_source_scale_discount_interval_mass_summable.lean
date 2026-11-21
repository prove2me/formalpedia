-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_discount_interval_mass_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:30:54.121185+00:00
-- url     : https://prove2.me/submissions/739d90e1-72d9-436a-a53a-cd7eca28f6fe

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_compact_factorial_majorant
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    Summable (fun n : ℕ =>
      ∫ y in (0 : ℝ)..x,
        q ^ n * scaleConvolutionPower (W 0) n y) := by
  have hu : Summable (fun n : ℕ =>
      (W 0 x * x) * ((q * x * W 0 x) ^ n /
        (Nat.factorial n : ℝ))) :=
    (Real.summable_pow_div_factorial (q * x * W 0 x)).mul_left _
  have hdom : ∀ n : ℕ,
      ‖∫ y in (0 : ℝ)..x,
        q ^ n * scaleConvolutionPower (W 0) n y‖ ≤
      (W 0 x * x) * ((q * x * W 0 x) ^ n /
        (Nat.factorial n : ℝ)) := by
    intro n
    have hbd : ∀ y ∈ Set.uIoc (0 : ℝ) x,
        ‖q ^ n * scaleConvolutionPower (W 0) n y‖ ≤
        W 0 x * (q * x * W 0 x) ^ n / (Nat.factorial n : ℝ) := by
      intro y hy
      have hy' : y ∈ Set.Ioc (0 : ℝ) x := by
        simpa only [Set.uIoc_of_le hx.le] using hy
      exact source_scale_compact_factorial_majorant
        ψ W hW q x hq hx.le n y ⟨hy'.1.le, hy'.2⟩
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    calc
      ‖∫ y in (0 : ℝ)..x, q ^ n * scaleConvolutionPower (W 0) n y‖ ≤
          (W 0 x * (q * x * W 0 x) ^ n /
            (Nat.factorial n : ℝ)) * |x - 0| := hnorm
      _ = (W 0 x * x) * ((q * x * W 0 x) ^ n /
            (Nat.factorial n : ℝ)) := by
          rw [sub_zero, abs_of_nonneg hx.le]
          ring
  have hdom' : ∀ n : ℕ,
      ‖∫ y in (0 : ℝ)..x,
        q ^ n * scaleConvolutionPower (W 0) n y‖ ≤
      (W 0 x * x) * ((q * x * W 0 x) ^ n /
        (Nat.factorial n : ℝ)) := hdom
  exact Summable.of_norm_bounded hu hdom'
