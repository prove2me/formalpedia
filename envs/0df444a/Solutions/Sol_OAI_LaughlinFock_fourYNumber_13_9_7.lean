-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_9_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:51:57.352108+00:00
-- url     : https://prove2.me/submissions/fc2945db-38d0-4bb8-93fe-899ec03093b3

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



theorem fourYNumber_13_9_7_oai :
    (collectedFourPartsTrace 13 9 7 collectedFourData_13 : ℚ) / fourCommonDenominator = (-45868939007172219785430914913/107374182400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_9_7_oai := @OAI.LaughlinFock.fourYNumber_13_9_7_oai
