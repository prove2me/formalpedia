-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_4_complete_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:50:58.732235+00:00
-- url     : https://prove2.me/submissions/fd74d2c9-e526-40fe-971c-10c9e471f6f9

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_4CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise44CompensatedJumpL2IsometryV3
set_option autoImplicit false

/-- Complete corrected exercise from its proved physical isometry. -/
theorem solution : Kyprianou.Ch04.certificate_exercise_4_4_v3 := by
  exact @Kyprianou.Ch04.exercise44CompensatedJumpL2IsometryV3
