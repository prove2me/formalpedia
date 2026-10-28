-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_5_5_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:11:14.544882+00:00
-- url     : https://prove2.me/submissions/ae4fc21d-f419-43e5-a2af-9394114ea9e3

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 5 5 (RowCompute.rows[6]!) =
    (14716655612190653211520800318771593624440728667029504000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
