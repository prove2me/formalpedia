-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_4_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:40:32.205345+00:00
-- url     : https://prove2.me/submissions/4fe0aa3c-4c70-498d-a952-c8e4b69d745e

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_technicalEsscherDensityConsistency_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_4_esscher_shifted_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_4_complex_extension_v2
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_result8_4 := by
  intro Ω mΩ P hP D ψ W hψ hW c hc
  exact ⟨
    source_technicalEsscherDensityConsistency_v2 Ω P D ψ c hψ hc,
    source_result8_4_esscher_shifted_v2 Ω P D ψ W hψ hW c hc,
    source_result8_4_complex_extension_v2 Ω P D ψ W hψ hW c hc⟩
