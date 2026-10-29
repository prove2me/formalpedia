-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_11_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:53:59.791988+00:00
-- url     : https://prove2.me/submissions/639926b1-53f1-4635-8d64-ec57bc40dc24

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 11 9 collectedFourData_15 : ℚ) / fourCommonDenominator = (-1547373619860320277277256763/1342177280000000000000000) := by
  decide +kernel
