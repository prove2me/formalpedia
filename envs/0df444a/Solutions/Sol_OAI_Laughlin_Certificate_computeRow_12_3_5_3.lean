-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:39:02.410618+00:00
-- url     : https://prove2.me/submissions/63ed9ac7-c5ca-4b04-873c-e328a5d74a41

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0305Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_5_3_oai : RowCompute.yRowIntegralFast 12 3 5 (RowCompute.rows[3]!) =
    (5189471267433044051469845232663260559540559953549852672000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_5_3_oai := @OAI.Laughlin.Certificate.computeRow_12_3_5_3_oai
