-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_7_complete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:59:20.91976+00:00
-- url     : https://prove2.me/submissions/9fdfd536-29c7-4319-aa55-4e117406015b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Theorems.Thm_Kyprianou_Ch04_exercise_4_7_i_goalV2
import Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
import Theorems.Thm_Kyprianou_Ch04_exercise_4_7_iii_goalV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch04

/-- Complete original textbook Exercise 4.7: every subpart. -/
theorem solution : certificate_exercise_4_7 := by
  exact ⟨
    Kyprianou.Ch04.exercise_4_7_i_goalV2,
    Kyprianou.Ch04.exercise47RunningSupremumIntegrable,
    Kyprianou.Ch04.exercise_4_7_iii_goalV2
  ⟩
