-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:49:29.160313+00:00
-- url     : https://prove2.me/submissions/0c6cf3d0-7b52-4eeb-a7a4-7ec6c3b637ad

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 5 3 collectedFourData_13 : ℚ) / fourCommonDenominator = (272608352002224246803257304523/13421772800000000000000000) := by
  decide +kernel
