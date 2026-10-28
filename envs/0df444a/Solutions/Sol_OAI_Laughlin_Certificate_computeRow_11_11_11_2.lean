-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_11_11_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:15:14.131375+00:00
-- url     : https://prove2.me/submissions/e619432c-f3a3-455c-ac50-1ee695ed29ee

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

theorem computeRow_11_11_11_2_oai : RowCompute.yRowIntegralFast 11 11 11 (RowCompute.rows[2]!) =
    (11538605281165693365016111754939488057493694015930045038592000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_11_11_2_oai := @OAI.Laughlin.Certificate.computeRow_11_11_11_2_oai
