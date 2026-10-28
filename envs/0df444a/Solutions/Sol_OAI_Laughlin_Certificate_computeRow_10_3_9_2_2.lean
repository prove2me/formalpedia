-- Prove2me | solution 2 for OAI.Laughlin.Certificate.computeRow_10_3_9_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:09.988408+00:00
-- url     : https://prove2.me/submissions/ffbe3a04-ce09-4463-a0c2-7e4c937b12b2

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 9 (RowCompute.rows[2]!) =
    (3391221475395966827639505721680643127647982444694680371200000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
