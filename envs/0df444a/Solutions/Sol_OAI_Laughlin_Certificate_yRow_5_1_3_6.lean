-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_3_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:04:11.171517+00:00
-- url     : https://prove2.me/submissions/8fbb383a-50a2-43fd-a34e-48411034bde6

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

theorem yRow_5_1_3_6_oai : yRow 5 1 3 (rows[6]!) = (-26195139147988314471 / 8388608 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_3_6_oai := @OAI.Laughlin.Certificate.yRow_5_1_3_6_oai
