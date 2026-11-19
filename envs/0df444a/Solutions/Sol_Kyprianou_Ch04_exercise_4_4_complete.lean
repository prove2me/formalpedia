-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_4_complete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:58:50.873366+00:00
-- url     : https://prove2.me/submissions/3166ddac-8d46-4fe0-92c1-fb82eeb95876
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_4Certification
import Theorems.Thm_Kyprianou_Ch04_exercise44CompensatedJumpL2Isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch04

/-- Complete original textbook Exercise 4.4: every subpart. -/
theorem solution : certificate_exercise_4_4 := by
  exact Kyprianou.Ch04.exercise44CompensatedJumpL2Isometry
