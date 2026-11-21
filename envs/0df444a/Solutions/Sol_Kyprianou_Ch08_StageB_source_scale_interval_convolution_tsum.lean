-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_interval_convolution_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:25:24.250825+00:00
-- url     : https://prove2.me/submissions/d6d22896-5f51-4c9e-a3dc-404ad824911b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_convolution_series
import Theorems.Thm_Kyprianou_Ch08_StageB_source_real_scale_series_interval_integral_exchange
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x : ℝ) (hx : 0 < x) (q : ℝ) (hq : 0 ≤ q) :
    Summable (fun n : ℕ => q ^ n *
      (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y)) ∧
    (∫ y in (0 : ℝ)..x, W q y) =
      ∑' n : ℕ, q ^ n *
        (∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) := by
  have hseries := source_real_scale_series_interval_integral_exchange
    ψ W hW x q hx hq
  have hreal : ∀ y : ℝ, 0 ≤ y →
      W q y = ∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n y := by
    intro y hy
    have hc := source_scale_discount_convolution_series ψ W hW y q hy hq
    have hcast :
        (((∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n y) : ℝ) : ℂ) =
          ∑' n : ℕ, (q : ℂ) ^ n *
            ((scaleConvolutionPower (W 0) n y : ℝ) : ℂ) := by
      simp only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow]
    exact Complex.ofReal_injective (hc.trans hcast.symm)
  have hInt :
      (∫ y in (0 : ℝ)..x, W q y) =
      (∫ y in (0 : ℝ)..x,
        ∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx.le] using hy
    exact hreal y hy'.1
  exact ⟨hseries.1, hInt.trans hseries.2⟩
