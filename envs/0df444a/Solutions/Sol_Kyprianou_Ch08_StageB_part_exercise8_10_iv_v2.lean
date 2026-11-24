-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_exercise8_10_iv_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:46:26.904885+00:00
-- url     : https://prove2.me/submissions/fe106e58-f878-45d3-b29c-b538507706e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_10_iii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_overshoot_payoff_reduction
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution : exercise8_10_iv := by
  intro Ω mΩ P hP D ψ W hψ hW hdrift
  obtain ⟨d, hd, hlast⟩ := part_exercise8_10_iii_v2 Ω P D ψ W hψ hW hdrift
  refine ⟨d, hd, fun q y hq hy => ?_⟩
  have he := p2m810_overshoot_payoff_reduction D ψ W hψ hW q hq y hy
  rw [hlast q y hq hy]
  linear_combination d * he
