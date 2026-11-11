-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_0_16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:53:19.3164+00:00
-- url     : https://prove2.me/submissions/c6110d59-8976-4a75-beeb-fa704b55864c

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_0_16_e_oai : Z 0 16 =
    ∑ k : Fin 27, lowerUnit entries k 0 * D k * lowerUnit entries k 16 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_0_16_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_0_16_e_oai
