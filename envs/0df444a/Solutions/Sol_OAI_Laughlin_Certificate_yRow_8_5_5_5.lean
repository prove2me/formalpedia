-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_5_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:13.191059+00:00
-- url     : https://prove2.me/submissions/996c0fab-355a-4d7f-b0f4-f99f5d307794

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 5 5 (rows[5]!) = (607875903328624705389525/469762048 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
