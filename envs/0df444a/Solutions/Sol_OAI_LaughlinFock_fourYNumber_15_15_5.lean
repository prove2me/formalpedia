-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_15_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:54:45.252124+00:00
-- url     : https://prove2.me/submissions/d8828efe-d7d5-427c-8972-c4cb9b074372

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 15 5 collectedFourData_15 : ℚ) / fourCommonDenominator = (30373191163661118559130314971/107374182400000000000000) := by
  decide +kernel
