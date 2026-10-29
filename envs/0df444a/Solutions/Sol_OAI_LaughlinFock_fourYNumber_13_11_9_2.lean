-- Prove2me | solution 2 for OAI.LaughlinFock.fourYNumber_13_11_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:56:20.845524+00:00
-- url     : https://prove2.me/submissions/a3513e62-85c7-45a1-b3bc-448c3eeb2785

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 11 9 collectedFourData_13 : ℚ) / fourCommonDenominator = (59787590378753456451814088133/53687091200000000000000000) := by
  decide +kernel
