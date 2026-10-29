-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:59:50.290423+00:00
-- url     : https://prove2.me/submissions/f25f8993-a666-49cb-834b-7c2c9a1af86d

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

theorem yRow_5_1_3_2_oai : yRow 5 1 3 (rows[2]!) = (3609794378028611869977 / 1879048192 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_3_2_oai := @OAI.Laughlin.Certificate.yRow_5_1_3_2_oai
