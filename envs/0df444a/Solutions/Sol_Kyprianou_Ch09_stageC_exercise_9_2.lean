-- Prove2me | solution 1 for Kyprianou.Ch09.stageC_exercise_9_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:48:11.777207+00:00
-- url     : https://prove2.me/submissions/e2a04401-1bd4-463b-8c9b-15fff0426c62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch09_SourceReflected
import Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_2_i
import Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_2_ii
import Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_2_iii
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch09
theorem solution :
  exercise9_2_i ∧ exercise9_2_ii ∧ exercise9_2_iii := by
  exact ⟨
    Kyprianou.Ch09.stageC_part_exercise_9_2_i,
    Kyprianou.Ch09.stageC_part_exercise_9_2_ii,
    Kyprianou.Ch09.stageC_part_exercise_9_2_iii
  ⟩
