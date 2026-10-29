-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_5_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:22.703607+00:00
-- url     : https://prove2.me/submissions/8650d7af-30f3-4bbc-aad7-1ad5df4c2061

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 5 5 (rows[2]!) = (106818877845876879555/2097152 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
