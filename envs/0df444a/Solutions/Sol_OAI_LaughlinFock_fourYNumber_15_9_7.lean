-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_9_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:58:42.434219+00:00
-- url     : https://prove2.me/submissions/504e56c3-66b8-4c74-9e8a-8a90075af443

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 9 7 collectedFourData_15 : ℚ) / fourCommonDenominator = (117089877007690980042457656891/13421772800000000000000000) := by
  decide +kernel
