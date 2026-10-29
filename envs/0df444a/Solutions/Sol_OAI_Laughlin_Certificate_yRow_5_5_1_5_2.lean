-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_5_1_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:40.144572+00:00
-- url     : https://prove2.me/submissions/796d8901-eaba-4180-880d-25a4f012df0e

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 1 (rows[5]!) = (209580109115659324643705 / 3758096384 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
