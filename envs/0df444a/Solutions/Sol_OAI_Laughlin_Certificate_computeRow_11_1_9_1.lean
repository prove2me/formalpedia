-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_9_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:24:58.604407+00:00
-- url     : https://prove2.me/submissions/8f868aa2-f85b-4fe6-9666-1e3718f84a26

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

theorem computeRow_11_1_9_1_oai : RowCompute.yRowIntegralFast 11 1 9 (RowCompute.rows[1]!) =
    (-36687004648015810181471356674478603470132329054208000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_9_1_oai := @OAI.Laughlin.Certificate.computeRow_11_1_9_1_oai
