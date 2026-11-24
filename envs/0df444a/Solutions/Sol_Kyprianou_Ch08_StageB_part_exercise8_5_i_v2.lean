-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_exercise8_5_i_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:31:39.805594+00:00
-- url     : https://prove2.me/submissions/95d410a2-7845-40dc-89a0-340625a5e89e

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_positive_discount_z_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_discount_coefficient_match
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_positive_discount_shift_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_discount_shift_ratio
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution : exercise8_5_i := by
  intro Ω mΩ P hP D ψ W hψ hW
  refine ⟨fun q hq => p2m85_positive_discount_z_ratio D ψ W hψ hW q hq,
    p2m85_zero_discount_coefficient_match D ψ W hψ hW, ?_⟩
  intro q x hq
  rcases hq.eq_or_lt with h | h
  · subst q
    exact p2m85_zero_discount_shift_ratio D ψ W hψ hW x
  · exact p2m85_positive_discount_shift_ratio D ψ W hψ hW q x h
