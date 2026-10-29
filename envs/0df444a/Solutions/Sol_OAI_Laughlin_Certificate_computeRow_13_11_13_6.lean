-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_11_13_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:49:38.827003+00:00
-- url     : https://prove2.me/submissions/8fe92e04-4bab-4e3a-ad79-3b0c3170c5aa

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1113Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_13_11_13_6_oai : RowCompute.yRowIntegralFast 13 11 13 (RowCompute.rows[6]!) =
    (115748950472124979530920403547368256240476286062692401152000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_13_11_13_6_oai := @OAI.Laughlin.Certificate.computeRow_13_11_13_6_oai
