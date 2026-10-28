-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:02:13.592527+00:00
-- url     : https://prove2.me/submissions/8e71464e-2c4a-4988-b85a-7368e3cf8c24

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_9

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0117Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_1_17_0 : RowCompute.yRowIntegralFast 21 1 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_17_1 : RowCompute.yRowIntegralFast 21 1 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_17_2 : RowCompute.yRowIntegralFast 21 1 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_17_3 : RowCompute.yRowIntegralFast 21 1 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_17_4 : RowCompute.yRowIntegralFast 21 1 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_17_5 : RowCompute.yRowIntegralFast 21 1 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_17_6 : RowCompute.yRowIntegralFast 21 1 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0119Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_1_19_0 : RowCompute.yRowIntegralFast 21 1 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_19_1 : RowCompute.yRowIntegralFast 21 1 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_19_2 : RowCompute.yRowIntegralFast 21 1 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_19_3 : RowCompute.yRowIntegralFast 21 1 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_19_4 : RowCompute.yRowIntegralFast 21 1 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_19_5 : RowCompute.yRowIntegralFast 21 1 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_19_6 : RowCompute.yRowIntegralFast 21 1 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0121Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_1_21_0 : RowCompute.yRowIntegralFast 21 1 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_21_1 : RowCompute.yRowIntegralFast 21 1 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_21_2 : RowCompute.yRowIntegralFast 21 1 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_21_3 : RowCompute.yRowIntegralFast 21 1 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_21_4 : RowCompute.yRowIntegralFast 21 1 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_21_5 : RowCompute.yRowIntegralFast 21 1 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_1_21_6 : RowCompute.yRowIntegralFast 21 1 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0317Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_3_17_0 : RowCompute.yRowIntegralFast 21 3 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_17_1 : RowCompute.yRowIntegralFast 21 3 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_17_2 : RowCompute.yRowIntegralFast 21 3 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_17_3 : RowCompute.yRowIntegralFast 21 3 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_17_4 : RowCompute.yRowIntegralFast 21 3 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_17_5 : RowCompute.yRowIntegralFast 21 3 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_17_6 : RowCompute.yRowIntegralFast 21 3 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0319Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_3_19_0 : RowCompute.yRowIntegralFast 21 3 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_19_1 : RowCompute.yRowIntegralFast 21 3 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_19_2 : RowCompute.yRowIntegralFast 21 3 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_19_3 : RowCompute.yRowIntegralFast 21 3 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_19_4 : RowCompute.yRowIntegralFast 21 3 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_19_5 : RowCompute.yRowIntegralFast 21 3 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_19_6 : RowCompute.yRowIntegralFast 21 3 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0321Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_3_21_0 : RowCompute.yRowIntegralFast 21 3 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_21_1 : RowCompute.yRowIntegralFast 21 3 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_21_2 : RowCompute.yRowIntegralFast 21 3 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_21_3 : RowCompute.yRowIntegralFast 21 3 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_21_4 : RowCompute.yRowIntegralFast 21 3 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_21_5 : RowCompute.yRowIntegralFast 21 3 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_3_21_6 : RowCompute.yRowIntegralFast 21 3 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0517Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_5_17_0 : RowCompute.yRowIntegralFast 21 5 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_17_1 : RowCompute.yRowIntegralFast 21 5 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_17_2 : RowCompute.yRowIntegralFast 21 5 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_17_3 : RowCompute.yRowIntegralFast 21 5 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_17_4 : RowCompute.yRowIntegralFast 21 5 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_17_5 : RowCompute.yRowIntegralFast 21 5 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_17_6 : RowCompute.yRowIntegralFast 21 5 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0519Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_5_19_0 : RowCompute.yRowIntegralFast 21 5 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_19_1 : RowCompute.yRowIntegralFast 21 5 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_19_2 : RowCompute.yRowIntegralFast 21 5 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_19_3 : RowCompute.yRowIntegralFast 21 5 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_19_4 : RowCompute.yRowIntegralFast 21 5 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_19_5 : RowCompute.yRowIntegralFast 21 5 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_19_6 : RowCompute.yRowIntegralFast 21 5 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0521Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_5_21_0 : RowCompute.yRowIntegralFast 21 5 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_21_1 : RowCompute.yRowIntegralFast 21 5 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_21_2 : RowCompute.yRowIntegralFast 21 5 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_21_3 : RowCompute.yRowIntegralFast 21 5 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_21_4 : RowCompute.yRowIntegralFast 21 5 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_21_5 : RowCompute.yRowIntegralFast 21 5 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_5_21_6 : RowCompute.yRowIntegralFast 21 5 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0717Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_7_17_0 : RowCompute.yRowIntegralFast 21 7 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_17_1 : RowCompute.yRowIntegralFast 21 7 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_17_2 : RowCompute.yRowIntegralFast 21 7 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_17_3 : RowCompute.yRowIntegralFast 21 7 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_17_4 : RowCompute.yRowIntegralFast 21 7 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_17_5 : RowCompute.yRowIntegralFast 21 7 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_17_6 : RowCompute.yRowIntegralFast 21 7 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0719Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_7_19_0 : RowCompute.yRowIntegralFast 21 7 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_19_1 : RowCompute.yRowIntegralFast 21 7 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_19_2 : RowCompute.yRowIntegralFast 21 7 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_19_3 : RowCompute.yRowIntegralFast 21 7 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_19_4 : RowCompute.yRowIntegralFast 21 7 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_19_5 : RowCompute.yRowIntegralFast 21 7 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_19_6 : RowCompute.yRowIntegralFast 21 7 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0721Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_7_21_0 : RowCompute.yRowIntegralFast 21 7 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_21_1 : RowCompute.yRowIntegralFast 21 7 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_21_2 : RowCompute.yRowIntegralFast 21 7 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_21_3 : RowCompute.yRowIntegralFast 21 7 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_21_4 : RowCompute.yRowIntegralFast 21 7 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_21_5 : RowCompute.yRowIntegralFast 21 7 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_7_21_6 : RowCompute.yRowIntegralFast 21 7 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0917Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_9_17_0 : RowCompute.yRowIntegralFast 21 9 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_17_1 : RowCompute.yRowIntegralFast 21 9 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_17_2 : RowCompute.yRowIntegralFast 21 9 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_17_3 : RowCompute.yRowIntegralFast 21 9 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_17_4 : RowCompute.yRowIntegralFast 21 9 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_17_5 : RowCompute.yRowIntegralFast 21 9 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_17_6 : RowCompute.yRowIntegralFast 21 9 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0919Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_9_19_0 : RowCompute.yRowIntegralFast 21 9 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_19_1 : RowCompute.yRowIntegralFast 21 9 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_19_2 : RowCompute.yRowIntegralFast 21 9 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_19_3 : RowCompute.yRowIntegralFast 21 9 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_19_4 : RowCompute.yRowIntegralFast 21 9 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_19_5 : RowCompute.yRowIntegralFast 21 9 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_19_6 : RowCompute.yRowIntegralFast 21 9 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0921Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_9_21_0 : RowCompute.yRowIntegralFast 21 9 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_21_1 : RowCompute.yRowIntegralFast 21 9 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_21_2 : RowCompute.yRowIntegralFast 21 9 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_21_3 : RowCompute.yRowIntegralFast 21 9 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_21_4 : RowCompute.yRowIntegralFast 21 9 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_21_5 : RowCompute.yRowIntegralFast 21 9 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_9_21_6 : RowCompute.yRowIntegralFast 21 9 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1117Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_11_17_0 : RowCompute.yRowIntegralFast 21 11 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_17_1 : RowCompute.yRowIntegralFast 21 11 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_17_2 : RowCompute.yRowIntegralFast 21 11 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_17_3 : RowCompute.yRowIntegralFast 21 11 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_17_4 : RowCompute.yRowIntegralFast 21 11 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_17_5 : RowCompute.yRowIntegralFast 21 11 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_17_6 : RowCompute.yRowIntegralFast 21 11 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1119Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_11_19_0 : RowCompute.yRowIntegralFast 21 11 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_19_1 : RowCompute.yRowIntegralFast 21 11 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_19_2 : RowCompute.yRowIntegralFast 21 11 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_19_3 : RowCompute.yRowIntegralFast 21 11 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_19_4 : RowCompute.yRowIntegralFast 21 11 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_19_5 : RowCompute.yRowIntegralFast 21 11 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_19_6 : RowCompute.yRowIntegralFast 21 11 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1121Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_11_21_0 : RowCompute.yRowIntegralFast 21 11 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_21_1 : RowCompute.yRowIntegralFast 21 11 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_21_2 : RowCompute.yRowIntegralFast 21 11 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_21_3 : RowCompute.yRowIntegralFast 21 11 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_21_4 : RowCompute.yRowIntegralFast 21 11 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_21_5 : RowCompute.yRowIntegralFast 21 11 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_11_21_6 : RowCompute.yRowIntegralFast 21 11 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1317Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_13_17_0 : RowCompute.yRowIntegralFast 21 13 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_17_1 : RowCompute.yRowIntegralFast 21 13 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_17_2 : RowCompute.yRowIntegralFast 21 13 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_17_3 : RowCompute.yRowIntegralFast 21 13 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_17_4 : RowCompute.yRowIntegralFast 21 13 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_17_5 : RowCompute.yRowIntegralFast 21 13 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_17_6 : RowCompute.yRowIntegralFast 21 13 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1319Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_13_19_0 : RowCompute.yRowIntegralFast 21 13 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_19_1 : RowCompute.yRowIntegralFast 21 13 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_19_2 : RowCompute.yRowIntegralFast 21 13 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_19_3 : RowCompute.yRowIntegralFast 21 13 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_19_4 : RowCompute.yRowIntegralFast 21 13 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_19_5 : RowCompute.yRowIntegralFast 21 13 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_19_6 : RowCompute.yRowIntegralFast 21 13 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1321Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_13_21_0 : RowCompute.yRowIntegralFast 21 13 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_21_1 : RowCompute.yRowIntegralFast 21 13 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_21_2 : RowCompute.yRowIntegralFast 21 13 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_21_3 : RowCompute.yRowIntegralFast 21 13 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_21_4 : RowCompute.yRowIntegralFast 21 13 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_21_5 : RowCompute.yRowIntegralFast 21 13 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_13_21_6 : RowCompute.yRowIntegralFast 21 13 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1517Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_15_17_0 : RowCompute.yRowIntegralFast 21 15 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_17_1 : RowCompute.yRowIntegralFast 21 15 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_17_2 : RowCompute.yRowIntegralFast 21 15 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_17_3 : RowCompute.yRowIntegralFast 21 15 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_17_4 : RowCompute.yRowIntegralFast 21 15 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_17_5 : RowCompute.yRowIntegralFast 21 15 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_17_6 : RowCompute.yRowIntegralFast 21 15 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1519Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_15_19_0 : RowCompute.yRowIntegralFast 21 15 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_19_1 : RowCompute.yRowIntegralFast 21 15 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_19_2 : RowCompute.yRowIntegralFast 21 15 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_19_3 : RowCompute.yRowIntegralFast 21 15 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_19_4 : RowCompute.yRowIntegralFast 21 15 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_19_5 : RowCompute.yRowIntegralFast 21 15 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_19_6 : RowCompute.yRowIntegralFast 21 15 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1521Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_15_21_0 : RowCompute.yRowIntegralFast 21 15 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_21_1 : RowCompute.yRowIntegralFast 21 15 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_21_2 : RowCompute.yRowIntegralFast 21 15 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_21_3 : RowCompute.yRowIntegralFast 21 15 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_21_4 : RowCompute.yRowIntegralFast 21 15 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_21_5 : RowCompute.yRowIntegralFast 21 15 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_15_21_6 : RowCompute.yRowIntegralFast 21 15 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1717Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_17_17_0 : RowCompute.yRowIntegralFast 21 17 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_17_1 : RowCompute.yRowIntegralFast 21 17 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_17_2 : RowCompute.yRowIntegralFast 21 17 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_17_3 : RowCompute.yRowIntegralFast 21 17 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_17_4 : RowCompute.yRowIntegralFast 21 17 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_17_5 : RowCompute.yRowIntegralFast 21 17 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_17_6 : RowCompute.yRowIntegralFast 21 17 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1719Batch21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_21_17_19_0 : RowCompute.yRowIntegralFast 21 17 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_19_1 : RowCompute.yRowIntegralFast 21 17 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_19_2 : RowCompute.yRowIntegralFast 21 17 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_19_3 : RowCompute.yRowIntegralFast 21 17 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_19_4 : RowCompute.yRowIntegralFast 21 17 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_19_5 : RowCompute.yRowIntegralFast 21 17 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_21_17_19_6 : RowCompute.yRowIntegralFast 21 17 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

theorem Y_expand (D r s : ℕ) : Y D r s =
    -(yRow D r s (rows[0]!) + (yRow D r s (rows[1]!) +
      (yRow D r s (rows[2]!) + (yRow D r s (rows[3]!) +
        (yRow D r s (rows[4]!) + (yRow D r s (rows[5]!) +
          (yRow D r s (rows[6]!) + 0))))))) / (10^14 : ℚ) := by rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Integral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_eq_integral (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (ht : t ≤ 16) (hT : e.1 + e.2.1 + (f.1 + f.2.1 - t) ≤ 24) :
    yEntry D r s t e f = (yEntryIntegral D r s t e f : ℚ) / arithmeticScale := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at hT
  let T := p+j+(q+l-t)
  let z : ℤ := 1-2*((p : ℤ)+(j : ℤ)+(q+l-t : ℕ))+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r : ℤ)+(s : ℤ))/2
  have hz : 0 ≤ 64+z := by dsimp [z,T]; omega
  have hexp : 65-2*((p : ℤ)+(j : ℤ)+(q+l-t : ℕ))+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r : ℤ)+(s : ℤ))/2 = 64+z := by dsimp [z]; ring
  have hp : (2 : ℚ)^((64+z).toNat) = (2 : ℚ)^64 * (2 : ℚ)^z := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hz, zpow_add₀ (by norm_num)]
    norm_num
  have hTD : T-D ≤ 24 := by dsimp [T]; omega
  have hf : ((T-D).factorial : ℚ) * ((24 : ℕ).descFactorial (24-(T-D)) : ℚ) = (Nat.factorial 24 : ℚ) := by
    have hn := Nat.factorial_mul_descFactorial (n := 24) (k := 24-(T-D)) (by omega)
    rw [Nat.sub_sub_self hTD] at hn
    exact_mod_cast hn
  dsimp [yEntry, yEntryIntegral]
  split_ifs with hd
  · change _ = _ / arithmeticScale
    rw [hexp]
    push_cast
    rw [hp]
    change _ = _ / ((2 : ℚ)^64 * (Nat.factorial 24 : ℚ))
    rw [← hf]
    have hn : ((T-D).factorial : ℚ) ≠ 0 := by positivity
    have hm : ((24 : ℕ).descFactorial (24-(T-D)) : ℚ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hf
      exact (ne_of_gt (show (0 : ℚ) < (Nat.factorial 24 : ℚ) by positivity)) hf.symm
    change _ = _ / ((2 : ℚ)^64 * (((T-D).factorial : ℚ) * ((24 : ℕ).descFactorial (24-(T-D)) : ℚ)))
    field_simp
    ring
  · simp

private theorem sum_integral {Element : Type*} (xs : List Element) (f : Element → ℤ) (c : ℚ) :
    (xs.map (fun x => (f x : ℚ)/c)).sum = ((xs.map f).sum : ℚ)/c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

theorem yRow_eq_integral (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (ht : row.1 ≤ 16)
    (hT : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24) :
    yRow D r s row = (yRowIntegral D r s row : ℚ) / arithmeticScale := by
  unfold yRow yRowIntegral
  calc
    _ = (row.2.2.map (fun e => (row.2.2.map (fun f =>
        (yEntryIntegral D r s row.1 e f : ℚ)/arithmeticScale)).sum)).sum := by
      congr 1
      apply List.map_congr_left
      intro e he
      congr 1
      apply List.map_congr_left
      intro f hf
      exact yEntry_eq_integral D r s row.1 e f ht (hT e he f hf)
    _ = _ := by simp_rw [sum_integral]

theorem rows_integral_bounds : ∀ row ∈ rows, row.1 ≤ 16 ∧
    ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24 := by
  decide +kernel

theorem source_yRow_eq_integral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegral D r s (rows[n]!) : ℚ) / arithmeticScale := by
  have hm : rows[n]! ∈ rows := by
    interval_cases n <;> decide +kernel
  exact yRow_eq_integral D r s _ (rows_integral_bounds _ hm).1 (rows_integral_bounds _ hm).2

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FastChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem U_eq_fast (c z T p : ℕ) : U c z T p = UFast c z T p := by
  simp only [U, UFast, Nat.choose_eq_fast_choose]

theorem V_eq_fast (r D T p j k : ℕ) : V r D T p j k = VFast r D T p j k := by
  simp only [V, VFast, U_eq_fast]

theorem yEntryIntegral_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntryIntegral D r s t e f = yEntryIntegralFast D r s t e f := by
  simp only [yEntryIntegral, yEntryIntegralFast, V_eq_fast]

theorem yRowIntegral_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRowIntegral D r s row = yRowIntegralFast D r s row := by
  simp only [yRowIntegral, yRowIntegralFast, yEntryIntegral_eq_fast]

theorem source_yRow_eq_fastIntegral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegralFast D r s (rows[n]!) : ℚ) / arithmeticScale := by
  rw [source_yRow_eq_integral D r s n hn, yRowIntegral_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RowBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_yRow_eq_rowCompute (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (RowCompute.yRowIntegralFast D r s (RowCompute.rows[n]!) : ℚ) / arithmeticScale := by
  exact source_yRow_eq_fastIntegral D r s n hn

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_21_1_17 : Y 21 1 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 1 17 0 (by decide),
    source_yRow_eq_rowCompute 21 1 17 1 (by decide),
    source_yRow_eq_rowCompute 21 1 17 2 (by decide),
    source_yRow_eq_rowCompute 21 1 17 3 (by decide),
    source_yRow_eq_rowCompute 21 1 17 4 (by decide),
    source_yRow_eq_rowCompute 21 1 17 5 (by decide),
    source_yRow_eq_rowCompute 21 1 17 6 (by decide),
    computeRow_21_1_17_0, computeRow_21_1_17_1, computeRow_21_1_17_2, computeRow_21_1_17_3, computeRow_21_1_17_4, computeRow_21_1_17_5, computeRow_21_1_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_1_19 : Y 21 1 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 1 19 0 (by decide),
    source_yRow_eq_rowCompute 21 1 19 1 (by decide),
    source_yRow_eq_rowCompute 21 1 19 2 (by decide),
    source_yRow_eq_rowCompute 21 1 19 3 (by decide),
    source_yRow_eq_rowCompute 21 1 19 4 (by decide),
    source_yRow_eq_rowCompute 21 1 19 5 (by decide),
    source_yRow_eq_rowCompute 21 1 19 6 (by decide),
    computeRow_21_1_19_0, computeRow_21_1_19_1, computeRow_21_1_19_2, computeRow_21_1_19_3, computeRow_21_1_19_4, computeRow_21_1_19_5, computeRow_21_1_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_1_21 : Y 21 1 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 1 21 0 (by decide),
    source_yRow_eq_rowCompute 21 1 21 1 (by decide),
    source_yRow_eq_rowCompute 21 1 21 2 (by decide),
    source_yRow_eq_rowCompute 21 1 21 3 (by decide),
    source_yRow_eq_rowCompute 21 1 21 4 (by decide),
    source_yRow_eq_rowCompute 21 1 21 5 (by decide),
    source_yRow_eq_rowCompute 21 1 21 6 (by decide),
    computeRow_21_1_21_0, computeRow_21_1_21_1, computeRow_21_1_21_2, computeRow_21_1_21_3, computeRow_21_1_21_4, computeRow_21_1_21_5, computeRow_21_1_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_3_17 : Y 21 3 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 3 17 0 (by decide),
    source_yRow_eq_rowCompute 21 3 17 1 (by decide),
    source_yRow_eq_rowCompute 21 3 17 2 (by decide),
    source_yRow_eq_rowCompute 21 3 17 3 (by decide),
    source_yRow_eq_rowCompute 21 3 17 4 (by decide),
    source_yRow_eq_rowCompute 21 3 17 5 (by decide),
    source_yRow_eq_rowCompute 21 3 17 6 (by decide),
    computeRow_21_3_17_0, computeRow_21_3_17_1, computeRow_21_3_17_2, computeRow_21_3_17_3, computeRow_21_3_17_4, computeRow_21_3_17_5, computeRow_21_3_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_3_19 : Y 21 3 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 3 19 0 (by decide),
    source_yRow_eq_rowCompute 21 3 19 1 (by decide),
    source_yRow_eq_rowCompute 21 3 19 2 (by decide),
    source_yRow_eq_rowCompute 21 3 19 3 (by decide),
    source_yRow_eq_rowCompute 21 3 19 4 (by decide),
    source_yRow_eq_rowCompute 21 3 19 5 (by decide),
    source_yRow_eq_rowCompute 21 3 19 6 (by decide),
    computeRow_21_3_19_0, computeRow_21_3_19_1, computeRow_21_3_19_2, computeRow_21_3_19_3, computeRow_21_3_19_4, computeRow_21_3_19_5, computeRow_21_3_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_3_21 : Y 21 3 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 3 21 0 (by decide),
    source_yRow_eq_rowCompute 21 3 21 1 (by decide),
    source_yRow_eq_rowCompute 21 3 21 2 (by decide),
    source_yRow_eq_rowCompute 21 3 21 3 (by decide),
    source_yRow_eq_rowCompute 21 3 21 4 (by decide),
    source_yRow_eq_rowCompute 21 3 21 5 (by decide),
    source_yRow_eq_rowCompute 21 3 21 6 (by decide),
    computeRow_21_3_21_0, computeRow_21_3_21_1, computeRow_21_3_21_2, computeRow_21_3_21_3, computeRow_21_3_21_4, computeRow_21_3_21_5, computeRow_21_3_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_5_17 : Y 21 5 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 5 17 0 (by decide),
    source_yRow_eq_rowCompute 21 5 17 1 (by decide),
    source_yRow_eq_rowCompute 21 5 17 2 (by decide),
    source_yRow_eq_rowCompute 21 5 17 3 (by decide),
    source_yRow_eq_rowCompute 21 5 17 4 (by decide),
    source_yRow_eq_rowCompute 21 5 17 5 (by decide),
    source_yRow_eq_rowCompute 21 5 17 6 (by decide),
    computeRow_21_5_17_0, computeRow_21_5_17_1, computeRow_21_5_17_2, computeRow_21_5_17_3, computeRow_21_5_17_4, computeRow_21_5_17_5, computeRow_21_5_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_5_19 : Y 21 5 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 5 19 0 (by decide),
    source_yRow_eq_rowCompute 21 5 19 1 (by decide),
    source_yRow_eq_rowCompute 21 5 19 2 (by decide),
    source_yRow_eq_rowCompute 21 5 19 3 (by decide),
    source_yRow_eq_rowCompute 21 5 19 4 (by decide),
    source_yRow_eq_rowCompute 21 5 19 5 (by decide),
    source_yRow_eq_rowCompute 21 5 19 6 (by decide),
    computeRow_21_5_19_0, computeRow_21_5_19_1, computeRow_21_5_19_2, computeRow_21_5_19_3, computeRow_21_5_19_4, computeRow_21_5_19_5, computeRow_21_5_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_5_21 : Y 21 5 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 5 21 0 (by decide),
    source_yRow_eq_rowCompute 21 5 21 1 (by decide),
    source_yRow_eq_rowCompute 21 5 21 2 (by decide),
    source_yRow_eq_rowCompute 21 5 21 3 (by decide),
    source_yRow_eq_rowCompute 21 5 21 4 (by decide),
    source_yRow_eq_rowCompute 21 5 21 5 (by decide),
    source_yRow_eq_rowCompute 21 5 21 6 (by decide),
    computeRow_21_5_21_0, computeRow_21_5_21_1, computeRow_21_5_21_2, computeRow_21_5_21_3, computeRow_21_5_21_4, computeRow_21_5_21_5, computeRow_21_5_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_7_17 : Y 21 7 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 7 17 0 (by decide),
    source_yRow_eq_rowCompute 21 7 17 1 (by decide),
    source_yRow_eq_rowCompute 21 7 17 2 (by decide),
    source_yRow_eq_rowCompute 21 7 17 3 (by decide),
    source_yRow_eq_rowCompute 21 7 17 4 (by decide),
    source_yRow_eq_rowCompute 21 7 17 5 (by decide),
    source_yRow_eq_rowCompute 21 7 17 6 (by decide),
    computeRow_21_7_17_0, computeRow_21_7_17_1, computeRow_21_7_17_2, computeRow_21_7_17_3, computeRow_21_7_17_4, computeRow_21_7_17_5, computeRow_21_7_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_7_19 : Y 21 7 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 7 19 0 (by decide),
    source_yRow_eq_rowCompute 21 7 19 1 (by decide),
    source_yRow_eq_rowCompute 21 7 19 2 (by decide),
    source_yRow_eq_rowCompute 21 7 19 3 (by decide),
    source_yRow_eq_rowCompute 21 7 19 4 (by decide),
    source_yRow_eq_rowCompute 21 7 19 5 (by decide),
    source_yRow_eq_rowCompute 21 7 19 6 (by decide),
    computeRow_21_7_19_0, computeRow_21_7_19_1, computeRow_21_7_19_2, computeRow_21_7_19_3, computeRow_21_7_19_4, computeRow_21_7_19_5, computeRow_21_7_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_7_21 : Y 21 7 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 7 21 0 (by decide),
    source_yRow_eq_rowCompute 21 7 21 1 (by decide),
    source_yRow_eq_rowCompute 21 7 21 2 (by decide),
    source_yRow_eq_rowCompute 21 7 21 3 (by decide),
    source_yRow_eq_rowCompute 21 7 21 4 (by decide),
    source_yRow_eq_rowCompute 21 7 21 5 (by decide),
    source_yRow_eq_rowCompute 21 7 21 6 (by decide),
    computeRow_21_7_21_0, computeRow_21_7_21_1, computeRow_21_7_21_2, computeRow_21_7_21_3, computeRow_21_7_21_4, computeRow_21_7_21_5, computeRow_21_7_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_9_17 : Y 21 9 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 9 17 0 (by decide),
    source_yRow_eq_rowCompute 21 9 17 1 (by decide),
    source_yRow_eq_rowCompute 21 9 17 2 (by decide),
    source_yRow_eq_rowCompute 21 9 17 3 (by decide),
    source_yRow_eq_rowCompute 21 9 17 4 (by decide),
    source_yRow_eq_rowCompute 21 9 17 5 (by decide),
    source_yRow_eq_rowCompute 21 9 17 6 (by decide),
    computeRow_21_9_17_0, computeRow_21_9_17_1, computeRow_21_9_17_2, computeRow_21_9_17_3, computeRow_21_9_17_4, computeRow_21_9_17_5, computeRow_21_9_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_9_19 : Y 21 9 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 9 19 0 (by decide),
    source_yRow_eq_rowCompute 21 9 19 1 (by decide),
    source_yRow_eq_rowCompute 21 9 19 2 (by decide),
    source_yRow_eq_rowCompute 21 9 19 3 (by decide),
    source_yRow_eq_rowCompute 21 9 19 4 (by decide),
    source_yRow_eq_rowCompute 21 9 19 5 (by decide),
    source_yRow_eq_rowCompute 21 9 19 6 (by decide),
    computeRow_21_9_19_0, computeRow_21_9_19_1, computeRow_21_9_19_2, computeRow_21_9_19_3, computeRow_21_9_19_4, computeRow_21_9_19_5, computeRow_21_9_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_9_21 : Y 21 9 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 9 21 0 (by decide),
    source_yRow_eq_rowCompute 21 9 21 1 (by decide),
    source_yRow_eq_rowCompute 21 9 21 2 (by decide),
    source_yRow_eq_rowCompute 21 9 21 3 (by decide),
    source_yRow_eq_rowCompute 21 9 21 4 (by decide),
    source_yRow_eq_rowCompute 21 9 21 5 (by decide),
    source_yRow_eq_rowCompute 21 9 21 6 (by decide),
    computeRow_21_9_21_0, computeRow_21_9_21_1, computeRow_21_9_21_2, computeRow_21_9_21_3, computeRow_21_9_21_4, computeRow_21_9_21_5, computeRow_21_9_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_11_17 : Y 21 11 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 11 17 0 (by decide),
    source_yRow_eq_rowCompute 21 11 17 1 (by decide),
    source_yRow_eq_rowCompute 21 11 17 2 (by decide),
    source_yRow_eq_rowCompute 21 11 17 3 (by decide),
    source_yRow_eq_rowCompute 21 11 17 4 (by decide),
    source_yRow_eq_rowCompute 21 11 17 5 (by decide),
    source_yRow_eq_rowCompute 21 11 17 6 (by decide),
    computeRow_21_11_17_0, computeRow_21_11_17_1, computeRow_21_11_17_2, computeRow_21_11_17_3, computeRow_21_11_17_4, computeRow_21_11_17_5, computeRow_21_11_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_11_19 : Y 21 11 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 11 19 0 (by decide),
    source_yRow_eq_rowCompute 21 11 19 1 (by decide),
    source_yRow_eq_rowCompute 21 11 19 2 (by decide),
    source_yRow_eq_rowCompute 21 11 19 3 (by decide),
    source_yRow_eq_rowCompute 21 11 19 4 (by decide),
    source_yRow_eq_rowCompute 21 11 19 5 (by decide),
    source_yRow_eq_rowCompute 21 11 19 6 (by decide),
    computeRow_21_11_19_0, computeRow_21_11_19_1, computeRow_21_11_19_2, computeRow_21_11_19_3, computeRow_21_11_19_4, computeRow_21_11_19_5, computeRow_21_11_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_11_21 : Y 21 11 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 11 21 0 (by decide),
    source_yRow_eq_rowCompute 21 11 21 1 (by decide),
    source_yRow_eq_rowCompute 21 11 21 2 (by decide),
    source_yRow_eq_rowCompute 21 11 21 3 (by decide),
    source_yRow_eq_rowCompute 21 11 21 4 (by decide),
    source_yRow_eq_rowCompute 21 11 21 5 (by decide),
    source_yRow_eq_rowCompute 21 11 21 6 (by decide),
    computeRow_21_11_21_0, computeRow_21_11_21_1, computeRow_21_11_21_2, computeRow_21_11_21_3, computeRow_21_11_21_4, computeRow_21_11_21_5, computeRow_21_11_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_13_17 : Y 21 13 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 13 17 0 (by decide),
    source_yRow_eq_rowCompute 21 13 17 1 (by decide),
    source_yRow_eq_rowCompute 21 13 17 2 (by decide),
    source_yRow_eq_rowCompute 21 13 17 3 (by decide),
    source_yRow_eq_rowCompute 21 13 17 4 (by decide),
    source_yRow_eq_rowCompute 21 13 17 5 (by decide),
    source_yRow_eq_rowCompute 21 13 17 6 (by decide),
    computeRow_21_13_17_0, computeRow_21_13_17_1, computeRow_21_13_17_2, computeRow_21_13_17_3, computeRow_21_13_17_4, computeRow_21_13_17_5, computeRow_21_13_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_13_19 : Y 21 13 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 13 19 0 (by decide),
    source_yRow_eq_rowCompute 21 13 19 1 (by decide),
    source_yRow_eq_rowCompute 21 13 19 2 (by decide),
    source_yRow_eq_rowCompute 21 13 19 3 (by decide),
    source_yRow_eq_rowCompute 21 13 19 4 (by decide),
    source_yRow_eq_rowCompute 21 13 19 5 (by decide),
    source_yRow_eq_rowCompute 21 13 19 6 (by decide),
    computeRow_21_13_19_0, computeRow_21_13_19_1, computeRow_21_13_19_2, computeRow_21_13_19_3, computeRow_21_13_19_4, computeRow_21_13_19_5, computeRow_21_13_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_13_21 : Y 21 13 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 13 21 0 (by decide),
    source_yRow_eq_rowCompute 21 13 21 1 (by decide),
    source_yRow_eq_rowCompute 21 13 21 2 (by decide),
    source_yRow_eq_rowCompute 21 13 21 3 (by decide),
    source_yRow_eq_rowCompute 21 13 21 4 (by decide),
    source_yRow_eq_rowCompute 21 13 21 5 (by decide),
    source_yRow_eq_rowCompute 21 13 21 6 (by decide),
    computeRow_21_13_21_0, computeRow_21_13_21_1, computeRow_21_13_21_2, computeRow_21_13_21_3, computeRow_21_13_21_4, computeRow_21_13_21_5, computeRow_21_13_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_15_17 : Y 21 15 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 15 17 0 (by decide),
    source_yRow_eq_rowCompute 21 15 17 1 (by decide),
    source_yRow_eq_rowCompute 21 15 17 2 (by decide),
    source_yRow_eq_rowCompute 21 15 17 3 (by decide),
    source_yRow_eq_rowCompute 21 15 17 4 (by decide),
    source_yRow_eq_rowCompute 21 15 17 5 (by decide),
    source_yRow_eq_rowCompute 21 15 17 6 (by decide),
    computeRow_21_15_17_0, computeRow_21_15_17_1, computeRow_21_15_17_2, computeRow_21_15_17_3, computeRow_21_15_17_4, computeRow_21_15_17_5, computeRow_21_15_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_15_19 : Y 21 15 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 15 19 0 (by decide),
    source_yRow_eq_rowCompute 21 15 19 1 (by decide),
    source_yRow_eq_rowCompute 21 15 19 2 (by decide),
    source_yRow_eq_rowCompute 21 15 19 3 (by decide),
    source_yRow_eq_rowCompute 21 15 19 4 (by decide),
    source_yRow_eq_rowCompute 21 15 19 5 (by decide),
    source_yRow_eq_rowCompute 21 15 19 6 (by decide),
    computeRow_21_15_19_0, computeRow_21_15_19_1, computeRow_21_15_19_2, computeRow_21_15_19_3, computeRow_21_15_19_4, computeRow_21_15_19_5, computeRow_21_15_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_15_21 : Y 21 15 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 15 21 0 (by decide),
    source_yRow_eq_rowCompute 21 15 21 1 (by decide),
    source_yRow_eq_rowCompute 21 15 21 2 (by decide),
    source_yRow_eq_rowCompute 21 15 21 3 (by decide),
    source_yRow_eq_rowCompute 21 15 21 4 (by decide),
    source_yRow_eq_rowCompute 21 15 21 5 (by decide),
    source_yRow_eq_rowCompute 21 15 21 6 (by decide),
    computeRow_21_15_21_0, computeRow_21_15_21_1, computeRow_21_15_21_2, computeRow_21_15_21_3, computeRow_21_15_21_4, computeRow_21_15_21_5, computeRow_21_15_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_17_17 : Y 21 17 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 17 17 0 (by decide),
    source_yRow_eq_rowCompute 21 17 17 1 (by decide),
    source_yRow_eq_rowCompute 21 17 17 2 (by decide),
    source_yRow_eq_rowCompute 21 17 17 3 (by decide),
    source_yRow_eq_rowCompute 21 17 17 4 (by decide),
    source_yRow_eq_rowCompute 21 17 17 5 (by decide),
    source_yRow_eq_rowCompute 21 17 17 6 (by decide),
    computeRow_21_17_17_0, computeRow_21_17_17_1, computeRow_21_17_17_2, computeRow_21_17_17_3, computeRow_21_17_17_4, computeRow_21_17_17_5, computeRow_21_17_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_21_17_19 : Y 21 17 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 21 17 19 0 (by decide),
    source_yRow_eq_rowCompute 21 17 19 1 (by decide),
    source_yRow_eq_rowCompute 21 17 19 2 (by decide),
    source_yRow_eq_rowCompute 21 17 19 3 (by decide),
    source_yRow_eq_rowCompute 21 17 19 4 (by decide),
    source_yRow_eq_rowCompute 21 17 19 5 (by decide),
    source_yRow_eq_rowCompute 21 17 19 6 (by decide),
    computeRow_21_17_19_0, computeRow_21_17_19_1, computeRow_21_17_19_2, computeRow_21_17_19_3, computeRow_21_17_19_4, computeRow_21_17_19_5, computeRow_21_17_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem error_21_oai : errorRational 21 = candidateY_21 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_21_1_1
  · exact source_error_21_1_3
  · exact source_error_21_1_5
  · exact source_error_21_1_7
  · exact source_error_21_1_9
  · exact source_error_21_1_11
  · exact source_error_21_1_13
  · exact source_error_21_1_15
  · exact source_error_21_1_17
  · exact source_error_21_1_19
  · exact source_error_21_1_21
  · exact source_error_21_3_1
  · exact source_error_21_3_3
  · exact source_error_21_3_5
  · exact source_error_21_3_7
  · exact source_error_21_3_9
  · exact source_error_21_3_11
  · exact source_error_21_3_13
  · exact source_error_21_3_15
  · exact source_error_21_3_17
  · exact source_error_21_3_19
  · exact source_error_21_3_21
  · exact source_error_21_5_1
  · exact source_error_21_5_3
  · exact source_error_21_5_5
  · exact source_error_21_5_7
  · exact source_error_21_5_9
  · exact source_error_21_5_11
  · exact source_error_21_5_13
  · exact source_error_21_5_15
  · exact source_error_21_5_17
  · exact source_error_21_5_19
  · exact source_error_21_5_21
  · exact source_error_21_7_1
  · exact source_error_21_7_3
  · exact source_error_21_7_5
  · exact source_error_21_7_7
  · exact source_error_21_7_9
  · exact source_error_21_7_11
  · exact source_error_21_7_13
  · exact source_error_21_7_15
  · exact source_error_21_7_17
  · exact source_error_21_7_19
  · exact source_error_21_7_21
  · exact source_error_21_9_1
  · exact source_error_21_9_3
  · exact source_error_21_9_5
  · exact source_error_21_9_7
  · exact source_error_21_9_9
  · exact source_error_21_9_11
  · exact source_error_21_9_13
  · exact source_error_21_9_15
  · exact source_error_21_9_17
  · exact source_error_21_9_19
  · exact source_error_21_9_21
  · exact source_error_21_11_1
  · exact source_error_21_11_3
  · exact source_error_21_11_5
  · exact source_error_21_11_7
  · exact source_error_21_11_9
  · exact source_error_21_11_11
  · exact source_error_21_11_13
  · exact source_error_21_11_15
  · exact source_error_21_11_17
  · exact source_error_21_11_19
  · exact source_error_21_11_21
  · exact source_error_21_13_1
  · exact source_error_21_13_3
  · exact source_error_21_13_5
  · exact source_error_21_13_7
  · exact source_error_21_13_9
  · exact source_error_21_13_11
  · exact source_error_21_13_13
  · exact source_error_21_13_15
  · exact source_error_21_13_17
  · exact source_error_21_13_19
  · exact source_error_21_13_21
  · exact source_error_21_15_1
  · exact source_error_21_15_3
  · exact source_error_21_15_5
  · exact source_error_21_15_7
  · exact source_error_21_15_9
  · exact source_error_21_15_11
  · exact source_error_21_15_13
  · exact source_error_21_15_15
  · exact source_error_21_15_17
  · exact source_error_21_15_19
  · exact source_error_21_15_21
  · exact source_error_21_17_1
  · exact source_error_21_17_3
  · exact source_error_21_17_5
  · exact source_error_21_17_7
  · exact source_error_21_17_9
  · exact source_error_21_17_11
  · exact source_error_21_17_13
  · exact source_error_21_17_15
  · exact source_error_21_17_17
  · exact source_error_21_17_19
  · exact source_error_21_17_21
  · exact source_error_21_19_1
  · exact source_error_21_19_3
  · exact source_error_21_19_5
  · exact source_error_21_19_7
  · exact source_error_21_19_9
  · exact source_error_21_19_11
  · exact source_error_21_19_13
  · exact source_error_21_19_15
  · exact source_error_21_19_17
  · exact source_error_21_19_19
  · exact source_error_21_19_21
  · exact source_error_21_21_1
  · exact source_error_21_21_3
  · exact source_error_21_21_5
  · exact source_error_21_21_7
  · exact source_error_21_21_9
  · exact source_error_21_21_11
  · exact source_error_21_21_13
  · exact source_error_21_21_15
  · exact source_error_21_21_17
  · exact source_error_21_21_19
  · exact source_error_21_21_21

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_21_oai := @OAI.Laughlin.Certificate.error_21_oai
