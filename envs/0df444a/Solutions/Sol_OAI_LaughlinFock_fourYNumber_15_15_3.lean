-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_15_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:02:28.374135+00:00
-- url     : https://prove2.me/submissions/3cb36a97-dd5f-4a94-937d-dd0f7fd5bfd7

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



theorem fourYNumber_15_15_3_oai :
    (collectedFourTrace 15 15 3 collectedFourData_15 : ℚ) / fourCommonDenominator = (-3452926424016985931403148463703/2684354560000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_15_3_oai := @OAI.LaughlinFock.fourYNumber_15_15_3_oai
