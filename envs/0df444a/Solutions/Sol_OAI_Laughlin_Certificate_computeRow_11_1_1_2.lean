-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:17:09.804133+00:00
-- url     : https://prove2.me/submissions/eb735157-6503-4fb3-bf02-866756866dc8

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

theorem computeRow_11_1_1_2_oai : RowCompute.yRowIntegralFast 11 1 1 (RowCompute.rows[2]!) =
    (-160293698295701288381312710735367011949318275968087883776000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_1_2_oai := @OAI.Laughlin.Certificate.computeRow_11_1_1_2_oai
