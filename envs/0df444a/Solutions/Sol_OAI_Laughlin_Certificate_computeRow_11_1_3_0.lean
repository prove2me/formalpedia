-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_3_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:18:39.811136+00:00
-- url     : https://prove2.me/submissions/0fc75f13-20b0-4440-a5ba-7b8eb38bb28c

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

theorem computeRow_11_1_3_0_oai : RowCompute.yRowIntegralFast 11 1 3 (RowCompute.rows[0]!) =
    (-12113043516412269861091912928363840447714978249110978560000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_3_0_oai := @OAI.Laughlin.Certificate.computeRow_11_1_3_0_oai
