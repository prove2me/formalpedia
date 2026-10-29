-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_1_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:56:06.142155+00:00
-- url     : https://prove2.me/submissions/3e9182eb-8c1a-4175-9c56-fb744ef424c5

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

theorem yRow_5_1_1_3_oai : yRow 5 1 1 (rows[3]!) = (-33527805633645391850149 / 939524096 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_1_3_oai := @OAI.Laughlin.Certificate.yRow_5_1_1_3_oai
