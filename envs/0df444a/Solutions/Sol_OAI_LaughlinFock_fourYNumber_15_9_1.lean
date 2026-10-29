-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_9_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:58:23.734696+00:00
-- url     : https://prove2.me/submissions/73eba6d0-cb82-4c1a-94b6-25a392750425

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 9 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (2848733507955651141700122589341/1677721600000000000000000) := by
  decide +kernel
