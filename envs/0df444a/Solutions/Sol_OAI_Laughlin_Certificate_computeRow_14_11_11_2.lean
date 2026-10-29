-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_11_11_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:52:03.838483+00:00
-- url     : https://prove2.me/submissions/da132d8f-9b02-42d0-bc7d-7dd8f2862fa3

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

theorem computeRow_14_11_11_2_oai : RowCompute.yRowIntegralFast 14 11 11 (RowCompute.rows[2]!) =
    (-3361804409470934976815286575571854038058592589603154165760000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_14_11_11_2_oai := @OAI.Laughlin.Certificate.computeRow_14_11_11_2_oai
