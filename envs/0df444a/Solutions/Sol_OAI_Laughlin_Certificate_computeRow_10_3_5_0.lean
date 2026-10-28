-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:19.833121+00:00
-- url     : https://prove2.me/submissions/e902d1e5-045b-4ce6-a789-0757a70651dc

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 5 (RowCompute.rows[0]!) =
    (785087747643110085317826568920274614519296809494380544000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
