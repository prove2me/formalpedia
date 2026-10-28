-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_11_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:59:20.883445+00:00
-- url     : https://prove2.me/submissions/00c21e4d-3b48-4e95-aa5d-de233419febe

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



theorem fourYNumber_15_11_1_oai :
    (collectedFourTrace 15 11 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (-5040016539767018277289956355221/3355443200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_11_1_oai := @OAI.LaughlinFock.fourYNumber_15_11_1_oai
