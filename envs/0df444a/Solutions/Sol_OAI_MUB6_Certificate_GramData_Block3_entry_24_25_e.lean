-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_24_25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:53:32.185634+00:00
-- url     : https://prove2.me/submissions/32a05a87-46a0-49dd-9b67-c259a322a587

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_24_25_e_oai : Z 24 25 =
    ∑ k : Fin 27, lowerUnit entries k 24 * D k * lowerUnit entries k 25 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_24_25_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_24_25_e_oai
