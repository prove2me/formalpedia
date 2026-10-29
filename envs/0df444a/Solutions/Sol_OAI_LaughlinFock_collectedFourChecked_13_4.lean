-- Prove2me | solution 1 for OAI.LaughlinFock.collectedFourChecked_13_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:43:37.474277+00:00
-- url     : https://prove2.me/submissions/adc87051-c883-4a54-a838-5e481a32f57a

import Mathlib
import Definitions.Def_OAIQ084L005

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1310. -/
namespace LaughlinFock

theorem collectedFourChecked_13_4_oai : collectNumericRowParts 13 4 = collectedFourData_13_4 := by
  decide +kernel

end LaughlinFock

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.collectedFourChecked_13_4_oai := @OAI.LaughlinFock.collectedFourChecked_13_4_oai
