-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_real_discount_series_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:22:25.972761+00:00
-- url     : https://prove2.me/submissions/54f4d07f-f04f-4f59-853b-5f250d2f1ccb

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∀ x : ℝ, 0 ≤
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) := by
  intro x
  apply tsum_nonneg
  intro n
  exact mul_nonneg (pow_nonneg hq _)
    (source_scale_power_nonnegative_all_real ψ W hW n x)
