-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_1_completeV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:58:19.444669+00:00
-- url     : https://prove2.me/submissions/8a340538-cbdb-44e4-bca1-41cfdfbe788a

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_1CertificationV2
import Theorems.Thm_Kyprianou_Ch04_exercise41ZeroVisitCounterCadlag
import Theorems.Thm_Kyprianou_Ch04_exercise_4_1_ii_goalV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch04

/-- Complete original textbook Exercise 4.1: every subpart. -/
theorem solution : certificate_exercise_4_1_v2 := by
  exact ⟨
    Kyprianou.Ch04.exercise41ZeroVisitCounterCadlag,
    Kyprianou.Ch04.exercise_4_1_ii_goalV2
  ⟩
