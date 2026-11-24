-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_result8_10_ii_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:13:03.017586+00:00
-- url     : https://prove2.me/submissions/3e248a6b-e7a4-4781-8602-76ce1c4fa70a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_ge_one
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_exit_ratio
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit reduction. -/
theorem solution :
    result8_10_ii := by
  unfold result8_10_ii
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa
  refine ⟨?_, p2m810_inf_exit_ratio Ω P D ψ W hψ hW q x a hq ha hx hxa⟩
  have h := source_zscale_ge_one ψ W hW q a hq ha.le
  linarith
