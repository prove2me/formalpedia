-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_real_discount_series_weighted_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:13:50.334493+00:00
-- url     : https://prove2.me/submissions/04a3d0e3-23b5-40ff-8f28-f4fcf4298854

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_discount_series_laplace_zero_q
import Theorems.Thm_Kyprianou_Ch08_StageB_source_discount_series_laplace_positive_q
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hroot0 : Phi ψ 0 < θ) (hrootq : Phi ψ q < θ) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
      (ψ θ - q)⁻¹ := by
  by_cases hzero : q = 0
  · subst q
    simpa only [sub_zero] using
      source_discount_series_laplace_zero_q ψ W hW θ hθ hroot0
  · have hpositive : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    exact source_discount_series_laplace_positive_q ψ W hW q θ
      hpositive hθ hroot0 hrootq
