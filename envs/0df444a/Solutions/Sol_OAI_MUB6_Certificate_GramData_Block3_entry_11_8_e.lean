-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_11_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:56:26.196947+00:00
-- url     : https://prove2.me/submissions/20d6f72a-c714-40f4-99ca-cab8bf0c3740

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_11_8_e_oai : Z 11 8 =
    ∑ k : Fin 27, lowerUnit entries k 11 * D k * lowerUnit entries k 8 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_11_8_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_11_8_e_oai
