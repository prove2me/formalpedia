-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:00.355738+00:00
-- url     : https://prove2.me/submissions/e498bda1-6ff9-4a49-b249-6d2b55187b24

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 9 (RowCompute.rows[4]!) =
    (584163568114117029845507681500030285567309322029262438400000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
