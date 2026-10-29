-- Prove2me | solution 1 for OAI.LaughlinFock.numericRowDataChecked_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:53:32.250304+00:00
-- url     : https://prove2.me/submissions/694baf38-78a4-4faa-9ddc-1d42955178be

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

theorem numericRowDataChecked_7_oai :
    rowEntryList_7.map (rowToNumeric ⟨7, by decide⟩) = numericRowData_7 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.numericRowDataChecked_7_oai := @OAI.LaughlinFock.numericRowDataChecked_7_oai
