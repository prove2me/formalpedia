-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_9_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:32:43.561686+00:00
-- url     : https://prove2.me/submissions/8d81ab68-cb57-4973-b2a9-bde34a1ce5e6

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0109Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_9_1_oai : RowCompute.yRowIntegralFast 12 1 9 (RowCompute.rows[1]!) =
    (-209211450120557088155707221993090560311272332086109798400000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_1_9_1_oai := @OAI.Laughlin.Certificate.computeRow_12_1_9_1_oai
