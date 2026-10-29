-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:58.32325+00:00
-- url     : https://prove2.me/submissions/fd620303-c84d-4d2b-8051-2e45b8322907

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 5 (rows[1]!) = (-18171099948981591081/2097152 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
