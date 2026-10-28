-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_5_11_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:15:02.341355+00:00
-- url     : https://prove2.me/submissions/98bb7b45-7dc2-446f-8c86-b717e6199f1a

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 5 11 (RowCompute.rows[1]!) =
    (-73608887966355807889726330727626087846046456157831168000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
