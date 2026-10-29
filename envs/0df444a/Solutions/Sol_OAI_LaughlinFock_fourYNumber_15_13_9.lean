-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_13_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:55:30.157975+00:00
-- url     : https://prove2.me/submissions/1307871b-04fa-494a-a3a9-6a147dc09d19

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 13 9 collectedFourData_15 : ℚ) / fourCommonDenominator = (28963210226166726601713556077/3355443200000000000000000) := by
  decide +kernel
