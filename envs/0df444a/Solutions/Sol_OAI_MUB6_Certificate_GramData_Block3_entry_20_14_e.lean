-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_20_14_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:22:02.466372+00:00
-- url     : https://prove2.me/submissions/484f21a2-3bd5-45b6-9e8d-20b427da147c

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_20_14_e_oai : Z 20 14 =
    ∑ k : Fin 27, lowerUnit entries k 20 * D k * lowerUnit entries k 14 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_20_14_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_20_14_e_oai
