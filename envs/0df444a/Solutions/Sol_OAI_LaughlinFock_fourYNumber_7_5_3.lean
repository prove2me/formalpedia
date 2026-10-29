-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_7_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:44:15.812439+00:00
-- url     : https://prove2.me/submissions/1d758ace-775d-41bd-9a1d-8210c5eba1a0

import Mathlib
import Definitions.Def_OAIQ084L015


open OAI OAI.LaughlinFock in
open scoped BigOperators Matrix ComplexOrder in
theorem solution :
    (shortNumericRowsFourTrace 7 5 3 : ℚ) / fourCommonDenominator = (1568403660783923680978370343/3006477107200000000000000000) := by
  decide +kernel
