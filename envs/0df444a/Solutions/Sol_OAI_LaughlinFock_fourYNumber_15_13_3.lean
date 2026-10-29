-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_13_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:56:32.141434+00:00
-- url     : https://prove2.me/submissions/037a2164-9b28-4a1f-a5cf-2bcc5d5e89c8

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 13 3 collectedFourData_15 : ℚ) / fourCommonDenominator = (40471219671864835802931462051/209715200000000000000000) := by
  decide +kernel
