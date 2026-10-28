-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_15_15_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:02:05.834068+00:00
-- url     : https://prove2.me/submissions/086f8d32-cfa6-468d-8766-e7cbef5aede4

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



theorem fourYNumber_15_15_15_oai :
    (collectedFourTrace 15 15 15 collectedFourData_15 : ℚ) / fourCommonDenominator = (-4368271789417477428222669736803/2147483648000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_15_15_15_oai := @OAI.LaughlinFock.fourYNumber_15_15_15_oai
