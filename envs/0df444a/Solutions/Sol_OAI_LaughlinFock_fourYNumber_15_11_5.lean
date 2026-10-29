-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:52:11.047915+00:00
-- url     : https://prove2.me/submissions/8c44fce8-a4d7-49ba-a9c2-59f7539c37dc

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 11 5 collectedFourData_15 : ℚ) / fourCommonDenominator = (41605607408434531382555260659/1342177280000000000000000) := by
  decide +kernel
