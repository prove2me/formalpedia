-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_weighted_series_terms_pointwise_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:18:07.00438+00:00
-- url     : https://prove2.me/submissions/d55d24ab-211a-4e75-b0c4-599002ae759b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_discount_series_summable_all_real
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) :
    ∀ x : ℝ, Summable (fun n : ℕ =>
      Real.exp (-(θ * x)) *
        (q ^ n * scaleConvolutionPower (W 0) n x)) := by
  intro x
  exact (source_discount_series_summable_all_real ψ W hW q hq x).mul_left _
