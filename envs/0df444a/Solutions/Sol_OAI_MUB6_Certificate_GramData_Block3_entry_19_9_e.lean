-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_19_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:17:29.439345+00:00
-- url     : https://prove2.me/submissions/30114531-1a4f-4afc-9e20-349da713eaeb

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

theorem entry_19_9_e_oai : Z 19 9 =
    ∑ k : Fin 27, lowerUnit entries k 19 * D k * lowerUnit entries k 9 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_19_9_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_19_9_e_oai
