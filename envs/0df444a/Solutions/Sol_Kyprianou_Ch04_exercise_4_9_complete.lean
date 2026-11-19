-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_9_complete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:59:41.989113+00:00
-- url     : https://prove2.me/submissions/accd5fbe-a605-4893-b070-e09f969d5bdb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvSmallTimeDrift
import Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvDownwardPersistence
import Theorems.Thm_Kyprianou_Ch04_exercise_4_9_iii_goalV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch04

/-- Complete original textbook Exercise 4.9: every subpart. -/
theorem solution : certificate_exercise_4_9 := by
  exact ⟨
    Kyprianou.Ch04.exercise49GeneralBvSmallTimeDrift,
    Kyprianou.Ch04.exercise49GeneralBvDownwardPersistence,
    Kyprianou.Ch04.exercise_4_9_iii_goalV2
  ⟩
