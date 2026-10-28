-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:32.100585+00:00
-- url     : https://prove2.me/submissions/47ef301b-3b2c-40bc-9af4-4dbe3831b33b

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 1 9 (RowCompute.rows[6]!) =
    (-364254855447306657548444315213067575151107961486154137600000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
