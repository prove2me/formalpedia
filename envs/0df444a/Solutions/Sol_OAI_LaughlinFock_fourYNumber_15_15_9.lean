-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_15_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:54:34.695331+00:00
-- url     : https://prove2.me/submissions/17e93626-ab47-4634-b4ba-141ed325c09d

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 15 9 collectedFourData_15 : ℚ) / fourCommonDenominator = (26896636911492553061456701101/2684354560000000000000000) := by
  decide +kernel
