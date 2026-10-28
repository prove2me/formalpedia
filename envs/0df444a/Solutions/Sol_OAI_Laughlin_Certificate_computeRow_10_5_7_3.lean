-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_5_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:50:06.127256+00:00
-- url     : https://prove2.me/submissions/d0e636ae-c406-4118-8f1d-f652d0cda6d7

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 5 7 (RowCompute.rows[3]!) =
    (115410589008732114243165504037203344187865671709753344000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
