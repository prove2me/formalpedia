-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_24_11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:29:45.44368+00:00
-- url     : https://prove2.me/submissions/c09c3ea4-f639-4024-a356-ba46866ab5ac

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_24_11_e_oai : Z 24 11 =
    ∑ k : Fin 27, lowerUnit entries k 24 * D k * lowerUnit entries k 11 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_24_11_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_24_11_e_oai
