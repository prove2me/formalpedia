-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:55.895996+00:00
-- url     : https://prove2.me/submissions/6e5870d6-d5de-45c4-891a-534ca3091504

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 3 (rows[4]!) = (-543574257899971267101 / 939524096 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
