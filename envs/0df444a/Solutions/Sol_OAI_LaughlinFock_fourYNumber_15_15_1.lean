-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_15_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:00:28.699515+00:00
-- url     : https://prove2.me/submissions/de8a6f91-7480-467f-989e-737f52ec61c8

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



theorem fourYNumber_15_15_1_oai :
    (collectedFourTrace 15 15 1 collectedFourData_15 : ℚ) / fourCommonDenominator = (-69774527590501029164523237379797/1342177280000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_15_1_oai := @OAI.LaughlinFock.fourYNumber_15_15_1_oai
