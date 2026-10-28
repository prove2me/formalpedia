-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:19:25.091487+00:00
-- url     : https://prove2.me/submissions/869e3196-395d-457a-8321-e1e1e62c9210

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

theorem computeRow_11_1_3_4_oai : RowCompute.yRowIntegralFast 11 1 3 (RowCompute.rows[4]!) =
    (-1879450322316792385483900622434737927990918917256118272000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_3_4_oai := @OAI.Laughlin.Certificate.computeRow_11_1_3_4_oai
