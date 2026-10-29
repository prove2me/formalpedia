-- Prove2me | solution 2 for OAI.LaughlinFock.fourYNumber_13_13_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:57:14.167655+00:00
-- url     : https://prove2.me/submissions/0e599183-8832-47a2-896e-b43d139b53e1

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 13 7 collectedFourData_13 : ℚ) / fourCommonDenominator = (-6961929908725446971605721289/21474836480000000000000000) := by
  decide +kernel
