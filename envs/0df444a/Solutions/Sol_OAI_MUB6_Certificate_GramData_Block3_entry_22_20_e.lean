-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_22_20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:52:14.880671+00:00
-- url     : https://prove2.me/submissions/b50d3ee8-f027-4960-8e12-a85924779eb2

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_22_20_e_oai : Z 22 20 =
    ∑ k : Fin 27, lowerUnit entries k 22 * D k * lowerUnit entries k 20 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_22_20_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_22_20_e_oai
