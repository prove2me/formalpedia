-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_9_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:47:32.481918+00:00
-- url     : https://prove2.me/submissions/f0a73bbf-26df-4c0b-a43c-fc5640b6c12d

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_9_9_e_oai : Z 9 9 =
    ∑ k : Fin 27, lowerUnit entries k 9 * D k * lowerUnit entries k 9 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_9_9_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_9_9_e_oai
