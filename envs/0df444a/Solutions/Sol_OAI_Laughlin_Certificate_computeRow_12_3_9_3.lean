-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_9_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:41:57.29758+00:00
-- url     : https://prove2.me/submissions/895a785e-ba9d-4c4f-aacb-56cac203118b

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0309Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_9_3_oai : RowCompute.yRowIntegralFast 12 3 9 (RowCompute.rows[3]!) =
    (-20883250032243841110909611672794518951974584419128180736000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_9_3_oai := @OAI.Laughlin.Certificate.computeRow_12_3_9_3_oai
