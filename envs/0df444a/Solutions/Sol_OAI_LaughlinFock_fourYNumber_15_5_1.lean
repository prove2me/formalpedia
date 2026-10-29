-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:57:02.287098+00:00
-- url     : https://prove2.me/submissions/4e433503-782f-402f-9ec5-285647254bc4

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 5 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (-121594567745064868354589107419/5242880000000000000000) := by
  decide +kernel
