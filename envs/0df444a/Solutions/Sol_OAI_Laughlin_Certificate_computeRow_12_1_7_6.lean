-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_7_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:30:55.550458+00:00
-- url     : https://prove2.me/submissions/d5974632-14f2-46a0-beb8-6ae9f76ba3bb

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0107Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_7_6_oai : RowCompute.yRowIntegralFast 12 1 7 (RowCompute.rows[6]!) =
    (-3626503373535045264582127330631780681595389982076305408000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_1_7_6_oai := @OAI.Laughlin.Certificate.computeRow_12_1_7_6_oai
