-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_9_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:06:28.495804+00:00
-- url     : https://prove2.me/submissions/0f18b071-88c1-42b2-b935-6d39958ddf92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_differentiable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_unrestricted_occupation_set_identity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08.StageB
/-- Assemble source 8.9 from Phi regularity and the full occupation identity. -/
theorem solution : sourceCertificate_result8_9 := by
  intro Ω mΩ P hP D ψ W hψ hW q x hq
  refine ⟨Kyprianou.Ch08.StageB.p2m89_phi_differentiable Ω P D ψ W hψ hW q hq, ?_⟩
  refine ⟨_, ?_, rfl⟩
  refine ⟨le_of_lt hq, ?_⟩
  intro A hA
  exact Kyprianou.Ch08.StageB.p2m89_unrestricted_occupation_set_identity Ω P D ψ W hψ hW q x hq A hA
