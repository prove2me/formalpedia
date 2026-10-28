-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:15:50.209585+00:00
-- url     : https://prove2.me/submissions/7e249321-9475-4bb0-94a0-a7e88fc267fe

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 3 3 (RowCompute.rows[2]!) =
    (-11226324742693615395743351897197717025809299935873885798400000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
