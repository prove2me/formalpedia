-- Prove2me | solution 1 for OAI.LaughlinFock.numericRowDataChecked_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:52:27.140987+00:00
-- url     : https://prove2.me/submissions/4e3f218c-4e96-4bee-baca-06dfaab2b14f

import Mathlib
import Definitions.Def_OAIQ084L015

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

theorem numericRowDataChecked_6_oai :
    rowEntryList_6.map (rowToNumeric ⟨6, by decide⟩) = numericRowData_6 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.numericRowDataChecked_6_oai := @OAI.LaughlinFock.numericRowDataChecked_6_oai
