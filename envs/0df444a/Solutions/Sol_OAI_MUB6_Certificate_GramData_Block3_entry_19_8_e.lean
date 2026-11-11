-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_19_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:17:28.234166+00:00
-- url     : https://prove2.me/submissions/79215067-3ecf-4f49-adf7-0d50d3d385b6

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_19_8_e_oai : Z 19 8 =
    ∑ k : Fin 27, lowerUnit entries k 19 * D k * lowerUnit entries k 8 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_19_8_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_19_8_e_oai
