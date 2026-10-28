-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_11_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:03:17.495866+00:00
-- url     : https://prove2.me/submissions/194ffe12-6af8-48d6-9c46-a769002d8620

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 12 1 11 (RowCompute.rows[3]!) =
    (-960924605880295885031213793410326379630898754448095444992000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
