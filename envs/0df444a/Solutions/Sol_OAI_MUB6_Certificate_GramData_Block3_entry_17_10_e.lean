-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_17_10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:04:22.63561+00:00
-- url     : https://prove2.me/submissions/a410c8ae-6764-4dca-b19f-48bcf1277c2a

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

theorem entry_17_10_e_oai : Z 17 10 =
    ∑ k : Fin 27, lowerUnit entries k 17 * D k * lowerUnit entries k 10 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_17_10_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_17_10_e_oai
