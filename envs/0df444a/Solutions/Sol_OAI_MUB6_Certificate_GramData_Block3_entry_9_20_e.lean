-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_9_20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:45:47.535141+00:00
-- url     : https://prove2.me/submissions/10cbb4f9-42b5-470d-9891-188f1d6eaef0

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

theorem entry_9_20_e_oai : Z 9 20 =
    ∑ k : Fin 27, lowerUnit entries k 9 * D k * lowerUnit entries k 20 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_9_20_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_9_20_e_oai
