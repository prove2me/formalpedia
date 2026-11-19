-- Prove2me | solution 1 for Kyprianou.Ch09.stageC_exercise_9_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:48:03.897284+00:00
-- url     : https://prove2.me/submissions/7a6ea729-b122-420a-b4e7-dced142f11ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch09_SourceMcKean
import Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_1_i
import Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_1_ii
import Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_1_iii
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch09
theorem solution :
  exercise9_1_i ∧ exercise9_1_ii ∧ exercise9_1_iii := by
  exact ⟨
    Kyprianou.Ch09.stageC_part_exercise_9_1_i,
    Kyprianou.Ch09.stageC_part_exercise_9_1_ii,
    Kyprianou.Ch09.stageC_part_exercise_9_1_iii
  ⟩
