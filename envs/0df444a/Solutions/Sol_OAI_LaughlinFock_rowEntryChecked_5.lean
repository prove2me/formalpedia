-- Prove2me | solution 1 for OAI.LaughlinFock.rowEntryChecked_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:54:39.118469+00:00
-- url     : https://prove2.me/submissions/e3e93544-2f3d-4ddb-8a0e-45fc97dad89e

import Mathlib
import Definitions.Def_OAIQ084L015

section
-- module Solutions.OAIQ084_LF.LaughlinFock_EntryEnumeration
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entry Enumeration. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem rowEntryChecked_5_oai : (Finset.univ : Finset (RowEntry 5)) = rowEntryData_5 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.rowEntryChecked_5_oai := @OAI.LaughlinFock.rowEntryChecked_5_oai
