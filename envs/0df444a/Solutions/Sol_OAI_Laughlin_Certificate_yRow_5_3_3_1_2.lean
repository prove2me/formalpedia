-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:52.900641+00:00
-- url     : https://prove2.me/submissions/29473b9e-703a-4891-a14c-958c35c9f127

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 3 (rows[1]!) = (12057655206433421045 / 234881024 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
