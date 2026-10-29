-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:37:55.436441+00:00
-- url     : https://prove2.me/submissions/1e5d3709-1f40-4721-926f-31c5d177773e

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

theorem computeRow_12_3_3_4_oai : RowCompute.yRowIntegralFast 12 3 3 (RowCompute.rows[4]!) =
    (-381886403076071442777717796594028700365785532393009971200000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_3_4_oai := @OAI.Laughlin.Certificate.computeRow_12_3_3_4_oai
