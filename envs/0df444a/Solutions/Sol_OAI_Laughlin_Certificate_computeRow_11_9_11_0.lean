-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_9_11_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:04:40.250805+00:00
-- url     : https://prove2.me/submissions/cb184d7a-7d92-4abd-ab0b-fb16ed52d6dd

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 9 11 (RowCompute.rows[0]!) =
    (-39725407016464938407731281496117765029876996456459534336000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
