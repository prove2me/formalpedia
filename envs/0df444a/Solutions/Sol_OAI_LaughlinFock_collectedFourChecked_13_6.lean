-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:44:22.475451+00:00
-- url     : https://prove2.me/submissions/c3eebbbf-51cc-43d9-8095-445b676466c8

import Mathlib
import Definitions.Def_OAIQ084L005

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1315. -/
namespace LaughlinFock

theorem collectedFourChecked_13_6_oai : collectNumericRowParts 13 6 = collectedFourData_13_6 := by
  decide +kernel

end LaughlinFock

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.collectedFourChecked_13_6_oai := @OAI.LaughlinFock.collectedFourChecked_13_6_oai
