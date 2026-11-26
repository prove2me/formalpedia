-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_2_complete
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:58:28.336828+00:00
-- url     : https://prove2.me/submissions/ad93eafc-63b9-44ab-bb89-348277ea4133

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_2Certification
import Theorems.Thm_Kyprianou_Ch04_exercise42SupremumChangeOfVariables
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch04

/-- Complete original textbook Exercise 4.2: every subpart. -/
theorem solution : certificate_exercise_4_2 := by
  exact Kyprianou.Ch04.exercise42SupremumChangeOfVariables
