-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_7_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:59:19.453924+00:00
-- url     : https://prove2.me/submissions/59f3a96e-eaec-4d60-882d-3dab20786230

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



theorem fourYNumber_14_7_7_oai :
    (collectedFourPartsTrace 14 7 7 collectedFourData_14 : ℚ) / fourCommonDenominator = (-124352718990572049190706318301/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_7_7_oai := @OAI.LaughlinFock.fourYNumber_14_7_7_oai
