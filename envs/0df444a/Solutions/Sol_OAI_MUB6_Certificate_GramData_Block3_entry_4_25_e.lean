-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_4_25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:36:36.294033+00:00
-- url     : https://prove2.me/submissions/7465bd24-4162-4621-a6bb-a804c217efd5

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_4_25_e_oai : Z 4 25 =
    ∑ k : Fin 27, lowerUnit entries k 4 * D k * lowerUnit entries k 25 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_4_25_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_4_25_e_oai
