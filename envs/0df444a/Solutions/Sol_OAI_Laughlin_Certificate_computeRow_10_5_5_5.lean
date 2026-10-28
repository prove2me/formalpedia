-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_5_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:50:12.551996+00:00
-- url     : https://prove2.me/submissions/b712e071-e7c7-4327-9f19-f409d415b2ec

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 5 5 (RowCompute.rows[5]!) =
    (3777761659438308842508575327729368613126130779553792000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
