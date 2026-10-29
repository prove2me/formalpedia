-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:52:48.237934+00:00
-- url     : https://prove2.me/submissions/f12db3f7-edcb-4ffb-aa75-c24a291dbd57

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 5 3 collectedFourData_15 : ℚ) / fourCommonDenominator = (154555932129637874044488648237/671088640000000000000000) := by
  decide +kernel
