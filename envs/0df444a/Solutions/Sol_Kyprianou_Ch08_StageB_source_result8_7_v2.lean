-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_7_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:05:54.829981+00:00
-- url     : https://prove2.me/submissions/a8e9f143-1800-44bd-89e3-8ba63b24748e

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_interval_occupation_set_identity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08.StageB
/-- Assemble source 8.7 from its measurable-set occupation identity. -/
theorem solution : sourceCertificate_result8_7 := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa
  refine ⟨_, ?_, rfl⟩
  refine ⟨hq, ha, ?_⟩
  intro A hA
  exact Kyprianou.Ch08.StageB.p2m87_interval_occupation_set_identity
    Ω P D ψ W hψ hW q a x hq ha hx hxa A hA
