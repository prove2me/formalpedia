-- Prove2me | solution 1 for OAI.LaughlinFock.numericRowDataChecked_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:49:31.176947+00:00
-- url     : https://prove2.me/submissions/f4c2fc98-fcb8-431e-a94e-62c2a30010be

import Mathlib
import Definitions.Def_OAIQ084L015
import Definitions.Def_OAIQ084L020

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NumericTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem numericRowDataChecked_0_oai :
    rowEntryList_0.map (rowToNumeric ⟨0, by decide⟩) = numericRowData_0 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.numericRowDataChecked_0_oai := @OAI.LaughlinFock.numericRowDataChecked_0_oai
