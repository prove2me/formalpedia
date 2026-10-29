-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:51.284799+00:00
-- url     : https://prove2.me/submissions/ad65c288-9df8-458a-bffa-98be6e841b45

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 5 (rows[3]!) = (16556987918363989467635 / 58720256 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
