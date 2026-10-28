-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_8_7_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:07:15.996881+00:00
-- url     : https://prove2.me/submissions/d9ffc38a-b8c4-4cd4-82e0-cde06735b81d

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_8_7_1_oai :
    (collectedFourPartsTrace 8 7 1 collectedFourData_8 : ℚ) / fourCommonDenominator = (-15409311511841483890426595631/2147483648000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_8_7_1_oai := @OAI.LaughlinFock.fourYNumber_8_7_1_oai
