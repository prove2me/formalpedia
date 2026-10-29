-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_5_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:48.388481+00:00
-- url     : https://prove2.me/submissions/9c85a83e-c8e3-4f0f-acbf-eb932bd2e886

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 5 (rows[1]!) = (105906315909713386913 / 58720256 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
