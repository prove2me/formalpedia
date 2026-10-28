-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:25.75322+00:00
-- url     : https://prove2.me/submissions/80cb24c2-d328-4608-905c-e60de853c73b

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 3 (RowCompute.rows[2]!) =
    (-1171996605828807486929619444190410224618081368112784998400000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
