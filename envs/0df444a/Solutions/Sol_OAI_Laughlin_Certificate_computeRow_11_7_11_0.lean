-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_7_11_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:10:55.818503+00:00
-- url     : https://prove2.me/submissions/08255925-818e-4f96-9353-d1bf977ce5b9

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 7 11 (RowCompute.rows[0]!) =
    (-17358638280715645790939812171653668799915859736738660352000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
