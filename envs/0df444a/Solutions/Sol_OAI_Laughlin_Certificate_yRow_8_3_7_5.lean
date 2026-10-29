-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_3_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:25.722899+00:00
-- url     : https://prove2.me/submissions/324f3ad7-e8e1-4c02-8d2c-d8434effff5f

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 3 7 (rows[5]!) = (-3479431231969799395785/8388608 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
