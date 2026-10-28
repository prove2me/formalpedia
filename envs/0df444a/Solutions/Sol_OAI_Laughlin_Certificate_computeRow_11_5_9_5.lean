-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_5_9_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:10:58.904347+00:00
-- url     : https://prove2.me/submissions/02824df7-a418-4999-8609-7ce0c3faa3fe

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 5 9 (RowCompute.rows[5]!) =
    (-7182984024030506601587495691905827957070692331028480000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
