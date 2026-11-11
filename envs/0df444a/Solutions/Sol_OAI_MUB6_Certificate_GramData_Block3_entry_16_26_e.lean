-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_16_26_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:04:16.258382+00:00
-- url     : https://prove2.me/submissions/18090ab3-df37-4ba7-b01e-47b0ed892512

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_16_26_e_oai : Z 16 26 =
    ∑ k : Fin 27, lowerUnit entries k 16 * D k * lowerUnit entries k 26 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_16_26_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_16_26_e_oai
