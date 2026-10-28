-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_7_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:15:19.379+00:00
-- url     : https://prove2.me/submissions/65f74619-bb47-4288-a702-aecf20e4a151

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 3 7 (RowCompute.rows[5]!) =
    (141150815255524124524449102027517769457374771795302809600000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
