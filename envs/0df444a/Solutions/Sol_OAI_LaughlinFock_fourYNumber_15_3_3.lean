-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:46:58.209446+00:00
-- url     : https://prove2.me/submissions/41e8a582-54eb-457d-9f14-838177838cf8

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 3 3 collectedFourData_15 : ℚ) / fourCommonDenominator = (-24176107214630877161809676787561/3355443200000000000000000) := by
  decide +kernel
