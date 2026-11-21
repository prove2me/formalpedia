-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result8_5_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:25:51.691935+00:00
-- url     : https://prove2.me/submissions/fb162d1e-d0a9-4983-bc75-d43c3a6efbe3

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_convolution_series_entire
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_convolution_series_agrees
set_option autoImplicit false

open Kyprianou.Ch08.StageB MeasureTheory

theorem solution : sourceCertificate_result8_5 := by
  intro ψ W hW x hx
  refine ⟨(fun z : ℂ => 1 + z * ∑' n : ℕ,
    z ^ n * (((∫ y in (0 : ℝ)..x,
      scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)), ?_, ?_⟩
  · exact source_zscale_convolution_series_entire ψ W hW x hx
  · intro q hq
    exact source_zscale_convolution_series_agrees ψ W hW x hx q hq
