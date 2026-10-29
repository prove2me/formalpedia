-- Prove2me | solution 1 for OAI.LaughlinFock.numericRowDataChecked_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:52:02.513676+00:00
-- url     : https://prove2.me/submissions/98d4d074-dfab-4567-ab7d-7a3aafff0fa7

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

theorem numericRowDataChecked_4_oai :
    rowEntryList_4.map (rowToNumeric ⟨4, by decide⟩) = numericRowData_4 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.numericRowDataChecked_4_oai := @OAI.LaughlinFock.numericRowDataChecked_4_oai
