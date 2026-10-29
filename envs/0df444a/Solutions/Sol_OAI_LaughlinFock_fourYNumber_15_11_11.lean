-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_11_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:45:48.267498+00:00
-- url     : https://prove2.me/submissions/0e83967b-62d2-4c11-a7b3-0f1803ffe255

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 11 11 collectedFourData_15 : ℚ) / fourCommonDenominator = (-3262167284765114930518367559/2684354560000000000000000) := by
  decide +kernel
