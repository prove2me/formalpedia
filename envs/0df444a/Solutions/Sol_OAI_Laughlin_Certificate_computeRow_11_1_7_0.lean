-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_7_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:22:02.569421+00:00
-- url     : https://prove2.me/submissions/339fa955-9bf9-4fb3-a193-336c1bc93ae9

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

theorem computeRow_11_1_7_0_oai : RowCompute.yRowIntegralFast 11 1 7 (RowCompute.rows[0]!) =
    (-19888044447852727867118888403642641513501084703994675200000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_7_0_oai := @OAI.Laughlin.Certificate.computeRow_11_1_7_0_oai
