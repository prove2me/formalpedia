-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_9_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:00:13.873465+00:00
-- url     : https://prove2.me/submissions/5f7689c8-1871-4281-b377-98d111c247cf

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 9 9 collectedFourData_15 : ℚ) / fourCommonDenominator = (-14666630048429445130453017813/3355443200000000000000000) := by
  decide +kernel
