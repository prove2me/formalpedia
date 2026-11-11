-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_12_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:59:06.738661+00:00
-- url     : https://prove2.me/submissions/e1d24e93-0055-45b7-b026-d53017842b92

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_12_8_e_oai : Z 12 8 =
    ∑ k : Fin 27, lowerUnit entries k 12 * D k * lowerUnit entries k 8 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_12_8_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_12_8_e_oai
