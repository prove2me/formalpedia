-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_1_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:10:16.872077+00:00
-- url     : https://prove2.me/submissions/6148f4cb-a0ea-4e5d-9834-33c8d1a339c3

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

theorem computeRow_10_1_1_6_oai : RowCompute.yRowIntegralFast 10 1 1 (RowCompute.rows[6]!) =
    (-702371643503080961776291898881618831906618893725073408000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_1_6_oai := @OAI.Laughlin.Certificate.computeRow_10_1_1_6_oai
