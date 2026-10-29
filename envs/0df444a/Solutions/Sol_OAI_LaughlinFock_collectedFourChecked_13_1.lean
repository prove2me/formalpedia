-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:42:52.599271+00:00
-- url     : https://prove2.me/submissions/5ca68715-423f-4689-81ce-6faaf001190b

import Mathlib
import Definitions.Def_OAIQ084L004

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1303
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1303. -/
namespace LaughlinFock

theorem collectedFourChecked_13_1_oai : collectNumericRowParts 13 1 = collectedFourData_13_1 := by
  decide +kernel

end LaughlinFock

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.collectedFourChecked_13_1_oai := @OAI.LaughlinFock.collectedFourChecked_13_1_oai
