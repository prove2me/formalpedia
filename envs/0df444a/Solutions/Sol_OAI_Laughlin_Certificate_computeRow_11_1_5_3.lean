-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:20:12.262673+00:00
-- url     : https://prove2.me/submissions/7c9e869b-e270-4d1b-994c-7d584c95608e

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_1_5_3_oai : RowCompute.yRowIntegralFast 11 1 5 (RowCompute.rows[3]!) =
    (-20301265734028949446653592867208114044880325168303439872000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_5_3_oai := @OAI.Laughlin.Certificate.computeRow_11_1_5_3_oai
