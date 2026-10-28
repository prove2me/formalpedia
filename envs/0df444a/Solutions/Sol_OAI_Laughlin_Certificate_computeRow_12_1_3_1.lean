-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:02:55.792981+00:00
-- url     : https://prove2.me/submissions/5dbc55a1-15c1-4313-a216-28ea01514cc1

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 12 1 3 (RowCompute.rows[1]!) =
    (-97370137542905594666079222280193552108036246430390681600000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
