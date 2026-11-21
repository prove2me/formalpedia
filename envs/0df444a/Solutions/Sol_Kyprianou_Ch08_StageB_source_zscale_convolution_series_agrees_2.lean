-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_zscale_convolution_series_agrees
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:25:40.124108+00:00
-- url     : https://prove2.me/submissions/daba9ca4-6873-49c0-aeaa-e69897543e72

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_interval_convolution_tsum
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (x : ℝ) (hx : 0 < x)
    (q : ℝ) (hq : 0 ≤ q) :
    (fun z : ℂ => 1 + z * ∑' n : ℕ,
        z ^ n * (((∫ y in (0 : ℝ)..x,
          scaleConvolutionPower (W 0) n y) : ℝ) : ℂ))
        (q : ℂ) = (Zscale q (W q) x : ℂ) := by
  have h := source_scale_interval_convolution_tsum ψ W hW x hx q hq
  change (1 : ℂ) + (q : ℂ) *
      (∑' n : ℕ, (q : ℂ) ^ n *
        (((∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)) =
      ((1 + q * (∫ y in (0 : ℝ)..x, W q y) : ℝ) : ℂ)
  rw [h.2]
  simp only [Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_tsum, Complex.ofReal_pow, Complex.ofReal_one]
