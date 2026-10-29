-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:59:22.477698+00:00
-- url     : https://prove2.me/submissions/c32ceaca-063a-4bb5-9a49-f3bce320e1ee

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 9 5 collectedFourData_15 : ℚ) / fourCommonDenominator = (803212446786638973149111013/167772160000000000000000) := by
  decide +kernel
