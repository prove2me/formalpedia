-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_discount_convolution_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:23:00.715781+00:00
-- url     : https://prove2.me/submissions/6cff7e71-d702-498b-a512-bfd6e3aeabb4

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_positive_x
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_at_zero
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ (x q : ℝ), 0 ≤ x → 0 ≤ q →
        ((W q x : ℝ) : ℂ) =
          ∑' n : ℕ, (q : ℂ) ^ n *
            ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ) := by
  intro ψ W hW x q hx hq
  by_cases hzero : x = 0
  · simpa only [hzero] using source_scale_discount_series_at_zero ψ W hW q hq
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    exact source_scale_discount_series_positive_x ψ W hW x q hxpos hq
