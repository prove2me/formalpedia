-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_13_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:45:22.886308+00:00
-- url     : https://prove2.me/submissions/2aa96614-ddde-4e15-802e-0c7e72237099

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 13 11 collectedFourData_15 : ℚ) / fourCommonDenominator = (2503653400615248264299638293/671088640000000000000000) := by
  decide +kernel
