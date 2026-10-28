-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_9_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:24:59.691985+00:00
-- url     : https://prove2.me/submissions/f94671e0-fea0-42f9-9c89-dbacba08ae7f

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

theorem computeRow_11_1_9_3_oai : RowCompute.yRowIntegralFast 11 1 9 (RowCompute.rows[3]!) =
    (-13936443411900935732457932883732614561400170841718652928000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_9_3_oai := @OAI.Laughlin.Certificate.computeRow_11_1_9_3_oai
