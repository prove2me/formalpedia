-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_7_11_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:05:12.595308+00:00
-- url     : https://prove2.me/submissions/1c5c5d65-35d7-4742-af46-e0ee0fcc628b

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 7 11 (RowCompute.rows[4]!) =
    (-14745398485742856139151904630225360542723873225834496000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
