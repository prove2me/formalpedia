-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_7_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:57:49.704996+00:00
-- url     : https://prove2.me/submissions/3d80a1f5-a1b6-45b5-a01c-28e3d2b56774

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 7 7 (rows[5]!) = (-45894925152507618987405/16777216 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
