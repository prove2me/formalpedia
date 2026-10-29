-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_5_7_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:10.008469+00:00
-- url     : https://prove2.me/submissions/ecb5a10d-ce8d-4479-bc8c-8798a0bd2d5d

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 5 7 (rows[2]!) = (-9014338390167069525885/1048576 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
