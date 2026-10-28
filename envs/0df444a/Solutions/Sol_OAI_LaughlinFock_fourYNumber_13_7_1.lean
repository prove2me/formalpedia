-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_7_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:50:27.784634+00:00
-- url     : https://prove2.me/submissions/ef65987c-77bf-4a52-882d-b63a96292238

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_13_7_1_oai :
    (collectedFourPartsTrace 13 7 1 collectedFourData_13 : ℚ) / fourCommonDenominator = (8652633863278216781156747661189/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_7_1_oai := @OAI.LaughlinFock.fourYNumber_13_7_1_oai
