-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_result8_10_i_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:14:06.767237+00:00
-- url     : https://prove2.me/submissions/2d6824b0-9bf5-46b3-bd1e-6d17928670c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_source_tilt_derivative
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_nonzero_transform
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_zero_payoff
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit reduction. -/
theorem solution :
    result8_10_i := by
  unfold result8_10_i
  intro Ω mΩ P hP D ψ W hψ hW q θ x a hq ha hx hxa hm
  exact ⟨(p2m810_source_tilt_derivative Ω P D ψ W hψ.1 hW q a θ hq ha).1,
    p2m810_sup_nonzero_transform Ω P D ψ W hψ hW q θ x a hq ha hx hxa hm,
    p2m810_sup_zero_payoff Ω P D ψ W hψ hW q θ x a hq ha hx hxa hm⟩
