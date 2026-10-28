-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:08:48.29858+00:00
-- url     : https://prove2.me/submissions/f79ddf55-7c58-4835-90c2-506a399c8ccc

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_10_1_1_1_oai : RowCompute.yRowIntegralFast 10 1 1 (RowCompute.rows[1]!) =
    (-13535534062307501855486080531491247876900223068196044800000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_1_1_oai := @OAI.Laughlin.Certificate.computeRow_10_1_1_1_oai
