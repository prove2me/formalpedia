-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_3_complete
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:58:40.544546+00:00
-- url     : https://prove2.me/submissions/61f338f7-647d-4726-9360-eebce80bb203
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_3Certification
import Theorems.Thm_Kyprianou_Ch04_exercise_4_3_i_goalV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_3_ii_goalV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_3_iii_goalV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_3_iv_goalV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch04

/-- Complete original textbook Exercise 4.3: every subpart. -/
theorem solution : certificate_exercise_4_3 := by
  exact ⟨
    Kyprianou.Ch04.exercise_4_3_i_goalV2,
    Kyprianou.Ch04.exercise_4_3_ii_goalV2,
    Kyprianou.Ch04.exercise_4_3_iii_goalV2,
    Kyprianou.Ch04.exercise_4_3_iv_goalV2
  ⟩
