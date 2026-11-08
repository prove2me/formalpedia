-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_16_23_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:40:42.330353+00:00
-- url     : https://prove2.me/submissions/cdf236cd-4fc5-4ca9-a48d-1ccf46a74a51

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_16_23_e_oai : Z 16 23 =
    ∑ k : Fin 27, lowerUnit entries k 16 * D k * lowerUnit entries k 23 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_16_23_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_16_23_e_oai
