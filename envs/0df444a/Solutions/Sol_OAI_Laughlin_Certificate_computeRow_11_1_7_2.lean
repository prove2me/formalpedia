-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_7_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:22:03.815783+00:00
-- url     : https://prove2.me/submissions/0aee2551-f791-449f-a230-64aecdaa03b9

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

theorem computeRow_11_1_7_2_oai : RowCompute.yRowIntegralFast 11 1 7 (RowCompute.rows[2]!) =
    (36482621736829736172280254524861935889826023996349480960000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_7_2_oai := @OAI.Laughlin.Certificate.computeRow_11_1_7_2_oai
