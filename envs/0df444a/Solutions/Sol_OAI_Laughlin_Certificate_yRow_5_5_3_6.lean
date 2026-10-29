-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:45.294405+00:00
-- url     : https://prove2.me/submissions/961189f1-2e4a-4712-934d-061a4ccbada6

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 3 (rows[6]!) = (-125595578390684976075 / 67108864 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
