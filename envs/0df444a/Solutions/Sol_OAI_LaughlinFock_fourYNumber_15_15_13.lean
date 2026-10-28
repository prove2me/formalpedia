-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_15_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:01:42.969303+00:00
-- url     : https://prove2.me/submissions/425d7ca6-be78-4060-ab7e-4264187f70b5

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



theorem fourYNumber_15_15_13_oai :
    (collectedFourTrace 15 15 13 collectedFourData_15 : ℚ) / fourCommonDenominator = (131081604324030412414565143941/1342177280000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_15_13_oai := @OAI.LaughlinFock.fourYNumber_15_15_13_oai
