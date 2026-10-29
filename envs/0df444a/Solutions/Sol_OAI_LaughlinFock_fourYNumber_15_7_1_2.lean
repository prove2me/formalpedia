-- Prove2me | solution 2 for OAI.LaughlinFock.fourYNumber_15_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:59:44.251283+00:00
-- url     : https://prove2.me/submissions/5bef0800-22ab-4f7c-8637-2f3655df1ee5

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 7 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (12612366434934957846304143447453/6710886400000000000000000) := by
  decide +kernel
