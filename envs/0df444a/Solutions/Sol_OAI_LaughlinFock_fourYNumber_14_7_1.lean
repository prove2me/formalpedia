-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_7_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:58:14.186156+00:00
-- url     : https://prove2.me/submissions/1b242e51-1cfd-4b82-a58c-6ce44d4e1570

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



theorem fourYNumber_14_7_1_oai :
    (collectedFourPartsTrace 14 7 1 collectedFourData_14 : ℚ) / fourCommonDenominator = (-601758946497245207677320475161/1342177280000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_7_1_oai := @OAI.LaughlinFock.fourYNumber_14_7_1_oai
