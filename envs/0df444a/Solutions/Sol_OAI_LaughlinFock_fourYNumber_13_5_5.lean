-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:44:43.807346+00:00
-- url     : https://prove2.me/submissions/cf84a759-38bf-4a24-810d-52db9fee8c51

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 5 5 collectedFourData_13 : ℚ) / fourCommonDenominator = (-12877898930642977749820839573/2684354560000000000000000) := by
  decide +kernel
