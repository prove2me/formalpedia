-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_5_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:57.200008+00:00
-- url     : https://prove2.me/submissions/3aab6c76-8602-4a10-b9d2-5fb4bacca6b1

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 5 5 (RowCompute.rows[0]!) =
    (-2095786808086228490108803423545225022048029421407830016000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
