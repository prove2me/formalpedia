-- Prove2me | solution 1 for OAI.LaughlinFock.numericRowDataChecked_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:52:05.087337+00:00
-- url     : https://prove2.me/submissions/34ba278f-8541-48e5-8fdd-11f993ff7b2d

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

theorem numericRowDataChecked_5_oai :
    rowEntryList_5.map (rowToNumeric ⟨5, by decide⟩) = numericRowData_5 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.numericRowDataChecked_5_oai := @OAI.LaughlinFock.numericRowDataChecked_5_oai
