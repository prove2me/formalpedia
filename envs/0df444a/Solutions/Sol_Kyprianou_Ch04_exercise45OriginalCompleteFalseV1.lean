-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45OriginalCompleteFalseV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:20:50.882996+00:00
-- url     : https://prove2.me/submissions/55b9aed3-35e6-48a7-aff6-1f17c4b51e04

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise45OriginalPartIVFalseV1
set_option autoImplicit false

/-- The conjunction of the four original certificates implies the false part (iv). -/
theorem solution : ¬ Kyprianou.Ch04.certificate_exercise_4_5V3 :=
  fun h => Kyprianou.Ch04.exercise45OriginalPartIVFalseV1 h.2.2.2
