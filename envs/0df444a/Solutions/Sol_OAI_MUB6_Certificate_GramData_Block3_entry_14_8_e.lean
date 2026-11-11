-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_14_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:02:15.834592+00:00
-- url     : https://prove2.me/submissions/197ef70b-c6fd-4bcc-a584-1a773ebfe7ed

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_14_8_e_oai : Z 14 8 =
    ∑ k : Fin 27, lowerUnit entries k 14 * D k * lowerUnit entries k 8 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_14_8_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_14_8_e_oai
