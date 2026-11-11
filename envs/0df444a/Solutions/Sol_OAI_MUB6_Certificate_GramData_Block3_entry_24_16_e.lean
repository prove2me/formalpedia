-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_24_16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:30:20.462184+00:00
-- url     : https://prove2.me/submissions/dd1f12aa-ece3-49f2-8be8-ddcf8a53cc48

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

theorem entry_24_16_e_oai : Z 24 16 =
    ∑ k : Fin 27, lowerUnit entries k 24 * D k * lowerUnit entries k 16 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_24_16_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_24_16_e_oai
