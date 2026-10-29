-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_1_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:39.586104+00:00
-- url     : https://prove2.me/submissions/ec9583ff-838d-4231-a367-f4f54014a426

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 1 (rows[1]!) = (-75316015709295173739/8388608 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
