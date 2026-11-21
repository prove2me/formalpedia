-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_zscale_convolution_series_entire
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:25:15.558799+00:00
-- url     : https://prove2.me/submissions/aed141f9-c824-4904-87f1-4a8693d5ab49

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_all_power_local_integrability
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_integrated_coefficient_bound
import Theorems.Thm_Kyprianou_Ch08_StageB_factorial_bounded_complex_series_entire
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (x : ℝ) (hx : 0 < x) :
    Differentiable ℂ
      (fun z : ℂ => 1 + z * ∑' n : ℕ,
        z ^ n * (((∫ y in (0 : ℝ)..x,
          scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)) := by
  let a : ℕ → ℝ := fun n =>
    ∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y
  let R : ℝ := x * W 0 x
  have hpos := (source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))).1 x
  have hR : 0 ≤ R := mul_nonneg hx.le hpos
  have hint := source_scale_all_power_local_integrability ψ W hW
  have hcoef : ∀ n : ℕ, ‖((a n : ℝ) : ℂ)‖ ≤
      R * R ^ n / (Nat.factorial n : ℝ) :=
    source_zscale_integrated_coefficient_bound ψ W hW hint x hx
  have hseries : Differentiable ℂ
      (fun z : ℂ => ∑' n : ℕ, z ^ n * ((a n : ℝ) : ℂ)) :=
    factorial_bounded_complex_series_entire a R R hR hR hcoef
  change Differentiable ℂ (fun z : ℂ => 1 + z *
    (∑' n : ℕ, z ^ n * ((a n : ℝ) : ℂ)))
  exact (differentiable_const (1 : ℂ)).add
    (differentiable_id.mul hseries)
