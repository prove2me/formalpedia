-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_5_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:11:03.163223+00:00
-- url     : https://prove2.me/submissions/85a15c8d-81e4-42d5-b7db-d8f90983e9d8

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

theorem computeRow_10_1_5_0_oai : RowCompute.yRowIntegralFast 10 1 5 (RowCompute.rows[0]!) =
    (-4702778694388233839698273005176170168040541342394220544000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_5_0_oai := @OAI.Laughlin.Certificate.computeRow_10_1_5_0_oai
