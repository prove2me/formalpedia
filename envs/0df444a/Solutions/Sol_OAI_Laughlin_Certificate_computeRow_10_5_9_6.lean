-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_5_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:49:53.29386+00:00
-- url     : https://prove2.me/submissions/824ae58c-aed2-44c1-abe2-ac7a3fab8a02

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 5 9 (RowCompute.rows[6]!) =
    (-37413140566972629346264960079870496141887957278654464000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
