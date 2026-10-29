-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:43:15.297003+00:00
-- url     : https://prove2.me/submissions/cf132dcb-db44-4d08-8fe7-0550a08db581

import Mathlib
import Definitions.Def_OAIQ084L004

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1306
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1306. -/
namespace LaughlinFock

theorem collectedFourChecked_13_2_oai : collectNumericRowParts 13 2 = collectedFourData_13_2 := by
  decide +kernel

end LaughlinFock

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.collectedFourChecked_13_2_oai := @OAI.LaughlinFock.collectedFourChecked_13_2_oai
