-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_17_15_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:05:32.911675+00:00
-- url     : https://prove2.me/submissions/a6c8631b-b630-423d-8874-bad9c64588a2

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

theorem entry_17_15_e_oai : Z 17 15 =
    ∑ k : Fin 27, lowerUnit entries k 17 * D k * lowerUnit entries k 15 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_17_15_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_17_15_e_oai
