-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_11_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:16:46.183749+00:00
-- url     : https://prove2.me/submissions/2a204250-a555-42c1-8095-c0b0d4160021

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_1_11_3_oai : RowCompute.yRowIntegralFast 11 1 11 (RowCompute.rows[3]!) =
    (-99002485888131387021866886415813759656647973238191685632000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_11_3_oai := @OAI.Laughlin.Certificate.computeRow_11_1_11_3_oai
