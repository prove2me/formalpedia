-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_7_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:12:31.527695+00:00
-- url     : https://prove2.me/submissions/5b6fa94a-2ecc-4668-9198-945cf2353a48

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_10_1_7_0_oai : RowCompute.yRowIntegralFast 10 1 7 (RowCompute.rows[0]!) =
    (8889277710280167816966690895860773693806705928586028646400000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_7_0_oai := @OAI.Laughlin.Certificate.computeRow_10_1_7_0_oai
