-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:44.4001+00:00
-- url     : https://prove2.me/submissions/1141b813-5b9b-484b-814c-c589f87aea15

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 5 (rows[3]!) = (-1676596742006268315615 / 117440512 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
