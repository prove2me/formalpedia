-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:54:25.155087+00:00
-- url     : https://prove2.me/submissions/5602be2a-6b5a-44ba-809b-9c58117c3d2f

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourPartsTrace 13 1 1 collectedFourData_13 : ℚ) / fourCommonDenominator = (54392955842088185147902038019563/6710886400000000000000000) := by
  decide +kernel
