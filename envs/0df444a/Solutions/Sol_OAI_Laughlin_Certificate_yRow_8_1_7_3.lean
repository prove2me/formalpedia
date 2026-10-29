-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:46.518273+00:00
-- url     : https://prove2.me/submissions/8e4f0d28-f9f3-4356-bbb8-53f1e5d80d45

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 7 (rows[3]!) = (58901045380419353591445/8388608 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
