-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_7_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:58:04.684781+00:00
-- url     : https://prove2.me/submissions/8983f836-a312-4bed-b13b-27b7c42b0a64

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate15Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_15_7_5_oai :
    (collectedFourTrace 15 7 5 collectedFourData_15 : ℚ) / fourCommonDenominator = (-23566822031129421592118634903/2684354560000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_7_5_oai := @OAI.LaughlinFock.fourYNumber_15_7_5_oai
