-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:52.226211+00:00
-- url     : https://prove2.me/submissions/9db8a315-db4b-4bb8-8606-7622f69780e3

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 5 (rows[5]!) = (-142185036639416818007445/67108864 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
