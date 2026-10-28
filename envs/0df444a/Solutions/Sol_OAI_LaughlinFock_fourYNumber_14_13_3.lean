-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_13_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:54:31.76205+00:00
-- url     : https://prove2.me/submissions/5b3eab26-049f-4778-be6a-265ef9d49501

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_14_13_3_oai :
    (collectedFourPartsTrace 14 13 3 collectedFourData_14 : ℚ) / fourCommonDenominator = (-339970341033955238226872051943/3355443200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_13_3_oai := @OAI.LaughlinFock.fourYNumber_14_13_3_oai
