-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:55:00.82084+00:00
-- url     : https://prove2.me/submissions/3878f7d6-48d7-4fe9-8518-aa7114fa9c64

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

theorem yRow_5_1_1_2_oai : yRow 5 1 1 (rows[2]!) = (45543850761592353716265 / 3758096384 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_1_2_oai := @OAI.Laughlin.Certificate.yRow_5_1_1_2_oai
