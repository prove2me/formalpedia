-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:50:13.333986+00:00
-- url     : https://prove2.me/submissions/3691f116-c358-45fd-9250-b058d9f1fe96

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 3 3 collectedFourData_13 : ℚ) / fourCommonDenominator = (549287455032456681750279702831/26843545600000000000000000) := by
  decide +kernel
