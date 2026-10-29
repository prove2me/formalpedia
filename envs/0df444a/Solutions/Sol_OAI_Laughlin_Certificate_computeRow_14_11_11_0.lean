-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_14_11_11_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:52:02.689755+00:00
-- url     : https://prove2.me/submissions/b01f3dd5-cbe4-4baa-bb4e-820909d7a735

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

theorem computeRow_14_11_11_0_oai : RowCompute.yRowIntegralFast 14 11 11 (RowCompute.rows[0]!) =
    (3114614113404638483619287775425405160664194096513102643200000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_14_11_11_0_oai := @OAI.Laughlin.Certificate.computeRow_14_11_11_0_oai
