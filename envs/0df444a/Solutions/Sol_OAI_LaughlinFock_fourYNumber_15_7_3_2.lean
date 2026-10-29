-- Prove2me | solution 2 for OAI.LaughlinFock.fourYNumber_15_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:58:08.617567+00:00
-- url     : https://prove2.me/submissions/0012cb18-ee8c-4ec2-9e29-2fbe7c22db2b

import Mathlib
import Definitions.Def_OAIQ084L022


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (collectedFourTrace 15 7 3 collectedFourData_15 : ℚ) / fourCommonDenominator = (773582640636166926582031618527/13421772800000000000000000) := by
  decide +kernel
