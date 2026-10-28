-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_7_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:30:10.3485+00:00
-- url     : https://prove2.me/submissions/fe530ad6-efc8-4e45-8719-f0f251d9091e

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0107Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_7_0_oai : RowCompute.yRowIntegralFast 12 1 7 (RowCompute.rows[0]!) =
    (-5436507894609498928122218552728205513229248405019033600000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_1_7_0_oai := @OAI.Laughlin.Certificate.computeRow_12_1_7_0_oai
