-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_9_completeV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:35:13.310656+00:00
-- url     : https://prove2.me/submissions/7cedc4ae-4e0c-4084-9669-91bd41c39603

import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvSmallTimeDrift
import Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvDownwardPersistence
import Theorems.Thm_Kyprianou_Ch04_exercise_4_9_iii_goalV3
open Kyprianou.Ch04
set_option autoImplicit false
/-- All three source subparts, with the almost-sure clock correction. -/
theorem solution : certificate_exercise_4_9_v3 := by
  exact ⟨@exercise49GeneralBvSmallTimeDrift,
    @exercise49GeneralBvDownwardPersistence, exercise_4_9_iii_goalV3⟩
