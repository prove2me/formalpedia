-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:56:44.984539+00:00
-- url     : https://prove2.me/submissions/092e68ad-10b4-4cc0-9e37-fee45b8041e6

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



theorem fourYNumber_14_3_1_oai :
    (collectedFourPartsTrace 14 3 1 collectedFourData_14 : ℚ) / fourCommonDenominator = (-13596265456695017190695318466177/838860800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_3_1_oai := @OAI.LaughlinFock.fourYNumber_14_3_1_oai
