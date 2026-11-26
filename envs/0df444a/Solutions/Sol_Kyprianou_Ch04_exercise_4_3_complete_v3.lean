-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_3_complete_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:15:45.638802+00:00
-- url     : https://prove2.me/submissions/b62a2f86-dfb4-4fc2-9b42-3b96443d4d27

import Definitions.Def_Kyprianou_Ch04_Exercise4_3CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise43GeneratorThresholdStoppingV3
import Theorems.Thm_Kyprianou_Ch04_exercise43StoppedCompensatedMartingaleV3
import Theorems.Thm_Kyprianou_Ch04_exercise43GeneratorIdentityV3
import Theorems.Thm_Kyprianou_Ch04_exercise_4_3_iv_goalV2

set_option autoImplicit false

open Kyprianou.Ch04

/-- Every corrected Exercise 4.3 subpart, with part (iv) unchanged. -/
theorem solution : certificate_exercise_4_3_v3 := by
  unfold certificate_exercise_4_3_v3
  exact ⟨@exercise43GeneratorThresholdStoppingV3,
    @exercise43StoppedCompensatedMartingaleV3,
    @exercise43GeneratorIdentityV3,
    exercise_4_3_iv_goalV2⟩
