-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_8_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:06:11.363192+00:00
-- url     : https://prove2.me/submissions/ccfe6736-9785-4dac-bcb6-62f742b7c66b

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_halfline_occupation_set_identity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08.StageB
/-- Assemble source 8.8 from its measurable-set half-line identity. -/
theorem solution : sourceCertificate_result8_8 := by
  intro Ω mΩ P hP D ψ W hψ hW q x hq hx
  refine ⟨_, ?_, rfl⟩
  refine ⟨hq, ?_⟩
  intro A hA
  exact Kyprianou.Ch08.StageB.p2m88_halfline_occupation_set_identity Ω P D ψ W hψ hW q x hq hx A hA
