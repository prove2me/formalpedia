-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_6_complete
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:59:11.20914+00:00
-- url     : https://prove2.me/submissions/f3774b93-e7d9-4ad3-81ae-87d363ae6b74

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_6Certification
import Theorems.Thm_Kyprianou_Ch04_exercise_4_6_i_goalV2
import Theorems.Thm_Kyprianou_Ch04_exercise_4_6_ii_goalV2
import Theorems.Thm_Kyprianou_Ch04_exercise46MM1StationaryWorkload
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch04

/-- Complete original textbook Exercise 4.6: every subpart. -/
theorem solution : certificate_exercise_4_6 := by
  exact ⟨
    Kyprianou.Ch04.exercise_4_6_i_goalV2,
    Kyprianou.Ch04.exercise_4_6_ii_goalV2,
    Kyprianou.Ch04.exercise46MM1StationaryWorkload
  ⟩
