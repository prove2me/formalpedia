-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_3_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:17.281728+00:00
-- url     : https://prove2.me/submissions/a0f305f1-3b2c-4edb-88fb-02636dde4fea

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 3 5 (rows[1]!) = (174426263694933807/524288 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
