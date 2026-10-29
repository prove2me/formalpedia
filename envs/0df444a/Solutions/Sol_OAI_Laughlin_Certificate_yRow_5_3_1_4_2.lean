-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_1_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:07:01.475045+00:00
-- url     : https://prove2.me/submissions/37cf9ecd-992c-4731-a62f-b09b9ac01dcc

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 1 (rows[4]!) = (973139460225276068975 / 939524096 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
