-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_13_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:51:57.857626+00:00
-- url     : https://prove2.me/submissions/10bef56d-3e2a-4f86-8477-f483ad37337f

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 13 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (6898076709287361794034590374623/1677721600000000000000000) := by
  decide +kernel
