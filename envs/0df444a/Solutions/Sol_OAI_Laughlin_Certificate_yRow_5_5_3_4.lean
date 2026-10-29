-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:53.926042+00:00
-- url     : https://prove2.me/submissions/32475f3c-c4d7-45d0-a895-abdec0ab6721

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 3 (rows[4]!) = (1122516649266680657945 / 939524096 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
