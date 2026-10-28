-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_3_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:19:47.833471+00:00
-- url     : https://prove2.me/submissions/3f79c82f-51f4-426e-b6bc-4dc092633b60

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

theorem computeRow_11_1_3_6_oai : RowCompute.yRowIntegralFast 11 1 3 (RowCompute.rows[6]!) =
    (428974078260461861878255711758104084753858113667334144000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_3_6_oai := @OAI.Laughlin.Certificate.computeRow_11_1_3_6_oai
