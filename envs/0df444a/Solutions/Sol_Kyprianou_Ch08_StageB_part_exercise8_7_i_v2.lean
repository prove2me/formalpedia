-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_exercise8_7_i_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:33:26.412413+00:00
-- url     : https://prove2.me/submissions/37c0ce6d-d6c4-4ee1-a79b-101fc7c2d416
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87ex_shifted_root_domain
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87ex_root_translation
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution : exercise8_7_i := by
  intro Ω mΩ P hP D ψ c q hψ hc hq
  exact p2m87ex_root_translation ψ c q hc
    (p2m87ex_shifted_root_domain D ψ hψ c q hc hq).1
