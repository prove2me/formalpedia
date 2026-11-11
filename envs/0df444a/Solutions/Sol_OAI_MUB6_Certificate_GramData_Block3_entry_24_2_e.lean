-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_24_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:53:29.393735+00:00
-- url     : https://prove2.me/submissions/472c91d8-43a0-4f28-a494-1945c2a809bd

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

theorem entry_24_2_e_oai : Z 24 2 =
    ∑ k : Fin 27, lowerUnit entries k 24 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_24_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_24_2_e_oai
