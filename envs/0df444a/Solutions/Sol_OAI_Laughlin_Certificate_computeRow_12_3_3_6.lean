-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_3_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:38:18.089587+00:00
-- url     : https://prove2.me/submissions/c10b1d9c-423a-45d6-af05-29d41c7fcd72

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0303Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_3_6_oai : RowCompute.yRowIntegralFast 12 3 3 (RowCompute.rows[6]!) =
    (-1217323579468315791335728871402140296511187494372166860800000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_3_6_oai := @OAI.Laughlin.Certificate.computeRow_12_3_3_6_oai
