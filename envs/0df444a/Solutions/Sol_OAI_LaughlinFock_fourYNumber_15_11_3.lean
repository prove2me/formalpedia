-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_11_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:45:36.222998+00:00
-- url     : https://prove2.me/submissions/53496d6a-88f4-439b-ac1c-3379ff6da7d4

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 11 3 collectedFourData_15 : ℚ) / fourCommonDenominator = (-430660873720800228400034708007/6710886400000000000000000) := by
  decide +kernel
