-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_11_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:55:44.895987+00:00
-- url     : https://prove2.me/submissions/e7cf6c61-d058-434b-8e7e-fb787f53285e

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



theorem fourYNumber_13_11_9_oai :
    (collectedFourPartsTrace 13 11 9 collectedFourData_13 : ℚ) / fourCommonDenominator = (59787590378753456451814088133/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_11_9_oai := @OAI.LaughlinFock.fourYNumber_13_11_9_oai
