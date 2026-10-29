-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_7_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:03.196507+00:00
-- url     : https://prove2.me/submissions/82b7fc48-6f2b-4868-91e0-6b2535c9de1c

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 7 7 (rows[1]!) = (-7376057539791286839/131072 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
