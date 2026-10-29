-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_1_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:57:56.062427+00:00
-- url     : https://prove2.me/submissions/d758ae83-e1bb-4434-9273-553248728ccc

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_5_1_1_6_oai : yRow 5 1 1 (rows[6]!) = (-192715136303794262991 / 33554432 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_1_6_oai := @OAI.Laughlin.Certificate.yRow_5_1_1_6_oai
