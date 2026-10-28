-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_11_11_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:15:15.946109+00:00
-- url     : https://prove2.me/submissions/138a1e11-c693-4e59-ada5-1bf64db94e45

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_11_11_4_oai : RowCompute.yRowIntegralFast 11 11 11 (RowCompute.rows[4]!) =
    (69566990712971699971921708105698186416006387497294626816000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_11_11_4_oai := @OAI.Laughlin.Certificate.computeRow_11_11_11_4_oai
