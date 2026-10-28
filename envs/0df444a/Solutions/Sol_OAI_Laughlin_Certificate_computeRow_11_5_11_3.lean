-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_5_11_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:11:35.631981+00:00
-- url     : https://prove2.me/submissions/e21ce1bc-be62-4b0f-909f-dd960070deea

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 5 11 (RowCompute.rows[3]!) =
    (27984412801626137700229212168997630850236334462730240000000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
