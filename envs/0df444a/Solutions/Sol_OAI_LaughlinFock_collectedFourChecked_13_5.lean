-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:43:38.387043+00:00
-- url     : https://prove2.me/submissions/059682c8-e119-454e-84a0-711e6ac94565

import Mathlib
import Definitions.Def_OAIQ084L005

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1313
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1313. -/
namespace LaughlinFock

theorem collectedFourChecked_13_5_oai : collectNumericRowParts 13 5 = collectedFourData_13_5 := by
  decide +kernel

end LaughlinFock

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.collectedFourChecked_13_5_oai := @OAI.LaughlinFock.collectedFourChecked_13_5_oai
