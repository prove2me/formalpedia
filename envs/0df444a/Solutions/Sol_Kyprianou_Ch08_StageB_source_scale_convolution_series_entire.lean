-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_convolution_series_entire
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:15:28.715815+00:00
-- url     : https://prove2.me/submissions/e5d5fe4c-4e59-4141-99b1-e28bfc1c9733

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_all_power_local_integrability
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_coeff_majorant
import Theorems.Thm_Kyprianou_Ch08_StageB_factorial_bounded_complex_series_entire
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ (x : ℝ), 0 ≤ x →
        Differentiable ℂ (fun z : ℂ =>
          ∑' n : ℕ, z ^ n *
            ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)) := by
  intro ψ W hW x hx
  have hmono := source_family_positive_monotone ψ W hW 0
      (le_refl (0 : ℝ))
  have hM : 0 ≤ W 0 x := hmono.1 x
  have hR : 0 ≤ x * W 0 x := mul_nonneg hx hM
  have hint := source_scale_all_power_local_integrability ψ W hW
  have hbound := source_scale_convolution_coeff_majorant ψ W hW hint x hx
  exact factorial_bounded_complex_series_entire
      (fun n => scaleConvolutionPower (W 0) n x)
      (W 0 x) (x * W 0 x) hM hR hbound
