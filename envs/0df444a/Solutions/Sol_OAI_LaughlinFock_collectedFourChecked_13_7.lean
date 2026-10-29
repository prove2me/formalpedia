-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:44:44.921074+00:00
-- url     : https://prove2.me/submissions/e2804457-70d6-4bea-9791-8faab948236a

import Mathlib
import Definitions.Def_OAIQ084L005

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1317. -/
namespace LaughlinFock

theorem collectedFourChecked_13_7_oai : collectNumericRowParts 13 7 = collectedFourData_13_7 := by
  decide +kernel

end LaughlinFock

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.collectedFourChecked_13_7_oai := @OAI.LaughlinFock.collectedFourChecked_13_7_oai
