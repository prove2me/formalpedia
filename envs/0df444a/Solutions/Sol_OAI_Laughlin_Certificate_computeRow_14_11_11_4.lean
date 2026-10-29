-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_11_11_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:52:25.683778+00:00
-- url     : https://prove2.me/submissions/3ebd0e07-ff6d-48ff-af9b-9e7efe6e9031

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1111Batch14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_14_11_11_4_oai : RowCompute.yRowIntegralFast 14 11 11 (RowCompute.rows[4]!) =
    (250982975863268616699691847899858177431504311564598509568000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_14_11_11_4_oai := @OAI.Laughlin.Certificate.computeRow_14_11_11_4_oai
