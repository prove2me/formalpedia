-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_11_11_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:15:17.153887+00:00
-- url     : https://prove2.me/submissions/429c20bb-d1b6-429d-9fbe-e1301941ed1a

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

theorem computeRow_11_11_11_6_oai : RowCompute.yRowIntegralFast 11 11 11 (RowCompute.rows[6]!) =
    (-3607923536242642674941290833548872569025237745739497472000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_11_11_6_oai := @OAI.Laughlin.Certificate.computeRow_11_11_11_6_oai
