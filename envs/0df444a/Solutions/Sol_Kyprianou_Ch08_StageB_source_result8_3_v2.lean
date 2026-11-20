-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_3_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:09:05.467011+00:00
-- url     : https://prove2.me/submissions/a447b9a5-0590-43cf-8391-8682faadf94f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_convolution_series
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_series_entire
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_result8_3 := by
  intro ψ W hW x hx
  refine ⟨(fun z : ℂ => ∑' n : ℕ, z ^ n *
      ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)), ?_, ?_⟩
  · exact source_scale_convolution_series_entire ψ W hW x hx
  · intro q hq
    exact (source_scale_discount_convolution_series ψ W hW x q hx hq).symm
