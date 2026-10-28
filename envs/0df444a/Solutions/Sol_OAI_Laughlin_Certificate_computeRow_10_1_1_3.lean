-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_1_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:09:11.132171+00:00
-- url     : https://prove2.me/submissions/1a67b1c1-f6d6-40b8-8198-a94ac77e1999

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

theorem computeRow_10_1_1_3_oai : RowCompute.yRowIntegralFast 10 1 1 (RowCompute.rows[3]!) =
    (-3786149587485340127194973991574971434714992935047056588800000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_1_3_oai := @OAI.Laughlin.Certificate.computeRow_10_1_1_3_oai
