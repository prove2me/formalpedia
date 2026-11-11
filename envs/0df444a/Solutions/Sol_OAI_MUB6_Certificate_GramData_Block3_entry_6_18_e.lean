-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_6_18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:39:39.99311+00:00
-- url     : https://prove2.me/submissions/4cd0befa-7a98-4de3-80e7-ebf4498e0744

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_6_18_e_oai : Z 6 18 =
    ∑ k : Fin 27, lowerUnit entries k 6 * D k * lowerUnit entries k 18 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_6_18_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_6_18_e_oai
