-- Prove2me | solution 1 for OAI.LaughlinFock.rowEntryChecked_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:53:54.976984+00:00
-- url     : https://prove2.me/submissions/6ca07b1c-cbc1-4c3c-ac1f-aac4054f80c8

import Mathlib
import Definitions.Def_OAIQ084L020

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

theorem rowEntryChecked_1_oai : (Finset.univ : Finset (RowEntry 1)) = rowEntryData_1 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.rowEntryChecked_1_oai := @OAI.LaughlinFock.rowEntryChecked_1_oai
