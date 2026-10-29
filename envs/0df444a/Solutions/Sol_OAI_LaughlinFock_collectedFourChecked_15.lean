-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_15
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:51:06.202068+00:00
-- url     : https://prove2.me/submissions/ffe3444c-de7f-450e-9974-0000758b281f

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution : collectedFourTerms 15 = collectedFourData_15 := by
  decide +kernel
