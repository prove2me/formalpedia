-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_17_24_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:06:43.763184+00:00
-- url     : https://prove2.me/submissions/7e4b23d8-4cd5-4cc9-96e9-3f5d5a70ed12

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_17_24_e_oai : Z 17 24 =
    ∑ k : Fin 27, lowerUnit entries k 17 * D k * lowerUnit entries k 24 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_17_24_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_17_24_e_oai
