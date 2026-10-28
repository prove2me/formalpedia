-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:06.558408+00:00
-- url     : https://prove2.me/submissions/d6e1ee81-6ef2-4897-a3d0-db09a3fe12e2

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 7 (RowCompute.rows[3]!) =
    (-538739484097491732485992836797273629839582415683374284800000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
