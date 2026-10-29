-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_3_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:59:48.102988+00:00
-- url     : https://prove2.me/submissions/bbac47f2-bd89-49d8-b575-a1e32c548749

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_5_1_3_0_oai : yRow 5 1 3 (rows[0]!) = (1227892611554313699 / 32768 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_3_0_oai := @OAI.Laughlin.Certificate.yRow_5_1_3_0_oai
