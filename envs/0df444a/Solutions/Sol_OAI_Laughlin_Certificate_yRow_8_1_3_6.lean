-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:55.374445+00:00
-- url     : https://prove2.me/submissions/8363f63a-4efe-4da6-8978-82a6971765f2

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 3 (rows[6]!) = (-397903947246140783805/4194304 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
