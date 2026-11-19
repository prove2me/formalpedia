-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_8_completeV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:59:30.831741+00:00
-- url     : https://prove2.me/submissions/5475ad86-153b-4e8a-b2ab-57a61b84dedf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_8_i_goalV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_8_ii_goalV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_8_iii_goalV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch04

/-- Complete original textbook Exercise 4.8: every subpart. -/
theorem solution : certificate_exercise_4_8_v2 := by
  exact ⟨
    Kyprianou.Ch04.exercise_4_8_i_goalV2,
    Kyprianou.Ch04.exercise_4_8_ii_goalV2,
    Kyprianou.Ch04.exercise_4_8_iii_goalV2
  ⟩
