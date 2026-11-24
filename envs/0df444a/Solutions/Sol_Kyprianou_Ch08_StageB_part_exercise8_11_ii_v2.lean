-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_exercise8_11_ii_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:29:40.4043+00:00
-- url     : https://prove2.me/submissions/ba6959a3-fe5a-4a85-868f-143420a85476
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_exit_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_ge_one
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
theorem solution : exercise8_11_ii := by
  intro Ω mΩ P hP D ψ W hψ hW hBV q x a hq ha hx hxa
  refine ⟨?_, p2m810_inf_exit_ratio Ω P D ψ W hψ hW q x a hq ha hx hxa⟩
  have h := source_zscale_ge_one ψ W hW q a hq ha.le
  linarith
