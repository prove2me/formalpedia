-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:37.750696+00:00
-- url     : https://prove2.me/submissions/5274ff0f-f020-47f5-b3a2-19acd6c6e5b4

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 7 (rows[5]!) = (100330787491458237454185/33554432 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
