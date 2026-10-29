-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_3_3_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:34.797825+00:00
-- url     : https://prove2.me/submissions/0308eaf0-a923-4f83-895f-95bc7b47122c

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 3 3 (rows[0]!) = (15977720834090203455/8192 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
