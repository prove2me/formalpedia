-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_20_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:20:36.226959+00:00
-- url     : https://prove2.me/submissions/51e909b8-2661-4c37-8f03-a45aa4f2da3e

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_20_2_e_oai : Z 20 2 =
    ∑ k : Fin 27, lowerUnit entries k 20 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_20_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_20_2_e_oai
