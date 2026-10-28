-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:05:54.43185+00:00
-- url     : https://prove2.me/submissions/b1cbd21c-ae09-4c4c-baa5-3d1cb1df319f

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_7

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0101Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_1_0 : RowCompute.yRowIntegralFast 23 1 1 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_1_1 : RowCompute.yRowIntegralFast 23 1 1 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_1_2 : RowCompute.yRowIntegralFast 23 1 1 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_1_3 : RowCompute.yRowIntegralFast 23 1 1 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_1_4 : RowCompute.yRowIntegralFast 23 1 1 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_1_5 : RowCompute.yRowIntegralFast 23 1 1 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_1_6 : RowCompute.yRowIntegralFast 23 1 1 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0103Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_3_0 : RowCompute.yRowIntegralFast 23 1 3 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_3_1 : RowCompute.yRowIntegralFast 23 1 3 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_3_2 : RowCompute.yRowIntegralFast 23 1 3 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_3_3 : RowCompute.yRowIntegralFast 23 1 3 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_3_4 : RowCompute.yRowIntegralFast 23 1 3 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_3_5 : RowCompute.yRowIntegralFast 23 1 3 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_3_6 : RowCompute.yRowIntegralFast 23 1 3 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0105Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_5_0 : RowCompute.yRowIntegralFast 23 1 5 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_5_1 : RowCompute.yRowIntegralFast 23 1 5 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_5_2 : RowCompute.yRowIntegralFast 23 1 5 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_5_3 : RowCompute.yRowIntegralFast 23 1 5 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_5_4 : RowCompute.yRowIntegralFast 23 1 5 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_5_5 : RowCompute.yRowIntegralFast 23 1 5 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_5_6 : RowCompute.yRowIntegralFast 23 1 5 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0107Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_7_0 : RowCompute.yRowIntegralFast 23 1 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_7_1 : RowCompute.yRowIntegralFast 23 1 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_7_2 : RowCompute.yRowIntegralFast 23 1 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_7_3 : RowCompute.yRowIntegralFast 23 1 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_7_4 : RowCompute.yRowIntegralFast 23 1 7 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_7_5 : RowCompute.yRowIntegralFast 23 1 7 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_7_6 : RowCompute.yRowIntegralFast 23 1 7 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0109Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_9_0 : RowCompute.yRowIntegralFast 23 1 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_9_1 : RowCompute.yRowIntegralFast 23 1 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_9_2 : RowCompute.yRowIntegralFast 23 1 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_9_3 : RowCompute.yRowIntegralFast 23 1 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_9_4 : RowCompute.yRowIntegralFast 23 1 9 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_9_5 : RowCompute.yRowIntegralFast 23 1 9 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_9_6 : RowCompute.yRowIntegralFast 23 1 9 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0111Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_11_0 : RowCompute.yRowIntegralFast 23 1 11 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_11_1 : RowCompute.yRowIntegralFast 23 1 11 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_11_2 : RowCompute.yRowIntegralFast 23 1 11 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_11_3 : RowCompute.yRowIntegralFast 23 1 11 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_11_4 : RowCompute.yRowIntegralFast 23 1 11 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_11_5 : RowCompute.yRowIntegralFast 23 1 11 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_11_6 : RowCompute.yRowIntegralFast 23 1 11 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0113Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_13_0 : RowCompute.yRowIntegralFast 23 1 13 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_13_1 : RowCompute.yRowIntegralFast 23 1 13 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_13_2 : RowCompute.yRowIntegralFast 23 1 13 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_13_3 : RowCompute.yRowIntegralFast 23 1 13 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_13_4 : RowCompute.yRowIntegralFast 23 1 13 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_13_5 : RowCompute.yRowIntegralFast 23 1 13 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_13_6 : RowCompute.yRowIntegralFast 23 1 13 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0115Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_15_0 : RowCompute.yRowIntegralFast 23 1 15 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_15_1 : RowCompute.yRowIntegralFast 23 1 15 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_15_2 : RowCompute.yRowIntegralFast 23 1 15 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_15_3 : RowCompute.yRowIntegralFast 23 1 15 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_15_4 : RowCompute.yRowIntegralFast 23 1 15 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_15_5 : RowCompute.yRowIntegralFast 23 1 15 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_15_6 : RowCompute.yRowIntegralFast 23 1 15 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0117Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_17_0 : RowCompute.yRowIntegralFast 23 1 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_17_1 : RowCompute.yRowIntegralFast 23 1 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_17_2 : RowCompute.yRowIntegralFast 23 1 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_17_3 : RowCompute.yRowIntegralFast 23 1 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_17_4 : RowCompute.yRowIntegralFast 23 1 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_17_5 : RowCompute.yRowIntegralFast 23 1 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_17_6 : RowCompute.yRowIntegralFast 23 1 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0119Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_19_0 : RowCompute.yRowIntegralFast 23 1 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_19_1 : RowCompute.yRowIntegralFast 23 1 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_19_2 : RowCompute.yRowIntegralFast 23 1 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_19_3 : RowCompute.yRowIntegralFast 23 1 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_19_4 : RowCompute.yRowIntegralFast 23 1 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_19_5 : RowCompute.yRowIntegralFast 23 1 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_19_6 : RowCompute.yRowIntegralFast 23 1 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0121Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_21_0 : RowCompute.yRowIntegralFast 23 1 21 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_21_1 : RowCompute.yRowIntegralFast 23 1 21 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_21_2 : RowCompute.yRowIntegralFast 23 1 21 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_21_3 : RowCompute.yRowIntegralFast 23 1 21 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_21_4 : RowCompute.yRowIntegralFast 23 1 21 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_21_5 : RowCompute.yRowIntegralFast 23 1 21 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_21_6 : RowCompute.yRowIntegralFast 23 1 21 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0123Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_1_23_0 : RowCompute.yRowIntegralFast 23 1 23 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_23_1 : RowCompute.yRowIntegralFast 23 1 23 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_23_2 : RowCompute.yRowIntegralFast 23 1 23 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_23_3 : RowCompute.yRowIntegralFast 23 1 23 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_23_4 : RowCompute.yRowIntegralFast 23 1 23 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_23_5 : RowCompute.yRowIntegralFast 23 1 23 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_1_23_6 : RowCompute.yRowIntegralFast 23 1 23 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0303Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_3_3_0 : RowCompute.yRowIntegralFast 23 3 3 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_3_1 : RowCompute.yRowIntegralFast 23 3 3 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_3_2 : RowCompute.yRowIntegralFast 23 3 3 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_3_3 : RowCompute.yRowIntegralFast 23 3 3 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_3_4 : RowCompute.yRowIntegralFast 23 3 3 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_3_5 : RowCompute.yRowIntegralFast 23 3 3 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_3_6 : RowCompute.yRowIntegralFast 23 3 3 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0305Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_3_5_0 : RowCompute.yRowIntegralFast 23 3 5 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_5_1 : RowCompute.yRowIntegralFast 23 3 5 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_5_2 : RowCompute.yRowIntegralFast 23 3 5 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_5_3 : RowCompute.yRowIntegralFast 23 3 5 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_5_4 : RowCompute.yRowIntegralFast 23 3 5 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_5_5 : RowCompute.yRowIntegralFast 23 3 5 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_5_6 : RowCompute.yRowIntegralFast 23 3 5 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0307Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_3_7_0 : RowCompute.yRowIntegralFast 23 3 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_7_1 : RowCompute.yRowIntegralFast 23 3 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_7_2 : RowCompute.yRowIntegralFast 23 3 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_7_3 : RowCompute.yRowIntegralFast 23 3 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_7_4 : RowCompute.yRowIntegralFast 23 3 7 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_7_5 : RowCompute.yRowIntegralFast 23 3 7 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_7_6 : RowCompute.yRowIntegralFast 23 3 7 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0309Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_3_9_0 : RowCompute.yRowIntegralFast 23 3 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_9_1 : RowCompute.yRowIntegralFast 23 3 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_9_2 : RowCompute.yRowIntegralFast 23 3 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_9_3 : RowCompute.yRowIntegralFast 23 3 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_9_4 : RowCompute.yRowIntegralFast 23 3 9 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_9_5 : RowCompute.yRowIntegralFast 23 3 9 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_9_6 : RowCompute.yRowIntegralFast 23 3 9 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0311Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_3_11_0 : RowCompute.yRowIntegralFast 23 3 11 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_11_1 : RowCompute.yRowIntegralFast 23 3 11 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_11_2 : RowCompute.yRowIntegralFast 23 3 11 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_11_3 : RowCompute.yRowIntegralFast 23 3 11 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_11_4 : RowCompute.yRowIntegralFast 23 3 11 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_11_5 : RowCompute.yRowIntegralFast 23 3 11 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_11_6 : RowCompute.yRowIntegralFast 23 3 11 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0313Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_3_13_0 : RowCompute.yRowIntegralFast 23 3 13 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_13_1 : RowCompute.yRowIntegralFast 23 3 13 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_13_2 : RowCompute.yRowIntegralFast 23 3 13 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_13_3 : RowCompute.yRowIntegralFast 23 3 13 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_13_4 : RowCompute.yRowIntegralFast 23 3 13 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_13_5 : RowCompute.yRowIntegralFast 23 3 13 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_13_6 : RowCompute.yRowIntegralFast 23 3 13 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0315Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_3_15_0 : RowCompute.yRowIntegralFast 23 3 15 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_15_1 : RowCompute.yRowIntegralFast 23 3 15 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_15_2 : RowCompute.yRowIntegralFast 23 3 15 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_15_3 : RowCompute.yRowIntegralFast 23 3 15 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_15_4 : RowCompute.yRowIntegralFast 23 3 15 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_15_5 : RowCompute.yRowIntegralFast 23 3 15 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_15_6 : RowCompute.yRowIntegralFast 23 3 15 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0317Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_3_17_0 : RowCompute.yRowIntegralFast 23 3 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_17_1 : RowCompute.yRowIntegralFast 23 3 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_17_2 : RowCompute.yRowIntegralFast 23 3 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_17_3 : RowCompute.yRowIntegralFast 23 3 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_17_4 : RowCompute.yRowIntegralFast 23 3 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_17_5 : RowCompute.yRowIntegralFast 23 3 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_3_17_6 : RowCompute.yRowIntegralFast 23 3 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0505Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_5_5_0 : RowCompute.yRowIntegralFast 23 5 5 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_5_1 : RowCompute.yRowIntegralFast 23 5 5 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_5_2 : RowCompute.yRowIntegralFast 23 5 5 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_5_3 : RowCompute.yRowIntegralFast 23 5 5 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_5_4 : RowCompute.yRowIntegralFast 23 5 5 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_5_5 : RowCompute.yRowIntegralFast 23 5 5 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_5_6 : RowCompute.yRowIntegralFast 23 5 5 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0507Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_5_7_0 : RowCompute.yRowIntegralFast 23 5 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_7_1 : RowCompute.yRowIntegralFast 23 5 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_7_2 : RowCompute.yRowIntegralFast 23 5 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_7_3 : RowCompute.yRowIntegralFast 23 5 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_7_4 : RowCompute.yRowIntegralFast 23 5 7 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_7_5 : RowCompute.yRowIntegralFast 23 5 7 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_7_6 : RowCompute.yRowIntegralFast 23 5 7 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0509Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_5_9_0 : RowCompute.yRowIntegralFast 23 5 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_9_1 : RowCompute.yRowIntegralFast 23 5 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_9_2 : RowCompute.yRowIntegralFast 23 5 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_9_3 : RowCompute.yRowIntegralFast 23 5 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_9_4 : RowCompute.yRowIntegralFast 23 5 9 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_9_5 : RowCompute.yRowIntegralFast 23 5 9 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_5_9_6 : RowCompute.yRowIntegralFast 23 5 9 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0707Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_7_7_0 : RowCompute.yRowIntegralFast 23 7 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_7_1 : RowCompute.yRowIntegralFast 23 7 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_7_2 : RowCompute.yRowIntegralFast 23 7 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_7_3 : RowCompute.yRowIntegralFast 23 7 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_7_4 : RowCompute.yRowIntegralFast 23 7 7 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_7_5 : RowCompute.yRowIntegralFast 23 7 7 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_7_6 : RowCompute.yRowIntegralFast 23 7 7 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0709Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_7_9_0 : RowCompute.yRowIntegralFast 23 7 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_9_1 : RowCompute.yRowIntegralFast 23 7 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_9_2 : RowCompute.yRowIntegralFast 23 7 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_9_3 : RowCompute.yRowIntegralFast 23 7 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_9_4 : RowCompute.yRowIntegralFast 23 7 9 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_9_5 : RowCompute.yRowIntegralFast 23 7 9 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_7_9_6 : RowCompute.yRowIntegralFast 23 7 9 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0909Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_23_9_9_0 : RowCompute.yRowIntegralFast 23 9 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_9_9_1 : RowCompute.yRowIntegralFast 23 9 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_9_9_2 : RowCompute.yRowIntegralFast 23 9 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_9_9_3 : RowCompute.yRowIntegralFast 23 9 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_9_9_4 : RowCompute.yRowIntegralFast 23 9 9 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_9_9_5 : RowCompute.yRowIntegralFast 23 9 9 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_23_9_9_6 : RowCompute.yRowIntegralFast 23 9 9 (RowCompute.rows[6]!) =
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem source_error_23_1_1 : Y 23 1 1 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 1 0 (by decide),
    source_yRow_eq_rowCompute 23 1 1 1 (by decide),
    source_yRow_eq_rowCompute 23 1 1 2 (by decide),
    source_yRow_eq_rowCompute 23 1 1 3 (by decide),
    source_yRow_eq_rowCompute 23 1 1 4 (by decide),
    source_yRow_eq_rowCompute 23 1 1 5 (by decide),
    source_yRow_eq_rowCompute 23 1 1 6 (by decide),
    computeRow_23_1_1_0, computeRow_23_1_1_1, computeRow_23_1_1_2, computeRow_23_1_1_3, computeRow_23_1_1_4, computeRow_23_1_1_5, computeRow_23_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_3 : Y 23 1 3 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 3 0 (by decide),
    source_yRow_eq_rowCompute 23 1 3 1 (by decide),
    source_yRow_eq_rowCompute 23 1 3 2 (by decide),
    source_yRow_eq_rowCompute 23 1 3 3 (by decide),
    source_yRow_eq_rowCompute 23 1 3 4 (by decide),
    source_yRow_eq_rowCompute 23 1 3 5 (by decide),
    source_yRow_eq_rowCompute 23 1 3 6 (by decide),
    computeRow_23_1_3_0, computeRow_23_1_3_1, computeRow_23_1_3_2, computeRow_23_1_3_3, computeRow_23_1_3_4, computeRow_23_1_3_5, computeRow_23_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_5 : Y 23 1 5 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 5 0 (by decide),
    source_yRow_eq_rowCompute 23 1 5 1 (by decide),
    source_yRow_eq_rowCompute 23 1 5 2 (by decide),
    source_yRow_eq_rowCompute 23 1 5 3 (by decide),
    source_yRow_eq_rowCompute 23 1 5 4 (by decide),
    source_yRow_eq_rowCompute 23 1 5 5 (by decide),
    source_yRow_eq_rowCompute 23 1 5 6 (by decide),
    computeRow_23_1_5_0, computeRow_23_1_5_1, computeRow_23_1_5_2, computeRow_23_1_5_3, computeRow_23_1_5_4, computeRow_23_1_5_5, computeRow_23_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_7 : Y 23 1 7 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 7 0 (by decide),
    source_yRow_eq_rowCompute 23 1 7 1 (by decide),
    source_yRow_eq_rowCompute 23 1 7 2 (by decide),
    source_yRow_eq_rowCompute 23 1 7 3 (by decide),
    source_yRow_eq_rowCompute 23 1 7 4 (by decide),
    source_yRow_eq_rowCompute 23 1 7 5 (by decide),
    source_yRow_eq_rowCompute 23 1 7 6 (by decide),
    computeRow_23_1_7_0, computeRow_23_1_7_1, computeRow_23_1_7_2, computeRow_23_1_7_3, computeRow_23_1_7_4, computeRow_23_1_7_5, computeRow_23_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_9 : Y 23 1 9 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 9 0 (by decide),
    source_yRow_eq_rowCompute 23 1 9 1 (by decide),
    source_yRow_eq_rowCompute 23 1 9 2 (by decide),
    source_yRow_eq_rowCompute 23 1 9 3 (by decide),
    source_yRow_eq_rowCompute 23 1 9 4 (by decide),
    source_yRow_eq_rowCompute 23 1 9 5 (by decide),
    source_yRow_eq_rowCompute 23 1 9 6 (by decide),
    computeRow_23_1_9_0, computeRow_23_1_9_1, computeRow_23_1_9_2, computeRow_23_1_9_3, computeRow_23_1_9_4, computeRow_23_1_9_5, computeRow_23_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_11 : Y 23 1 11 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 11 0 (by decide),
    source_yRow_eq_rowCompute 23 1 11 1 (by decide),
    source_yRow_eq_rowCompute 23 1 11 2 (by decide),
    source_yRow_eq_rowCompute 23 1 11 3 (by decide),
    source_yRow_eq_rowCompute 23 1 11 4 (by decide),
    source_yRow_eq_rowCompute 23 1 11 5 (by decide),
    source_yRow_eq_rowCompute 23 1 11 6 (by decide),
    computeRow_23_1_11_0, computeRow_23_1_11_1, computeRow_23_1_11_2, computeRow_23_1_11_3, computeRow_23_1_11_4, computeRow_23_1_11_5, computeRow_23_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_13 : Y 23 1 13 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 13 0 (by decide),
    source_yRow_eq_rowCompute 23 1 13 1 (by decide),
    source_yRow_eq_rowCompute 23 1 13 2 (by decide),
    source_yRow_eq_rowCompute 23 1 13 3 (by decide),
    source_yRow_eq_rowCompute 23 1 13 4 (by decide),
    source_yRow_eq_rowCompute 23 1 13 5 (by decide),
    source_yRow_eq_rowCompute 23 1 13 6 (by decide),
    computeRow_23_1_13_0, computeRow_23_1_13_1, computeRow_23_1_13_2, computeRow_23_1_13_3, computeRow_23_1_13_4, computeRow_23_1_13_5, computeRow_23_1_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_15 : Y 23 1 15 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 15 0 (by decide),
    source_yRow_eq_rowCompute 23 1 15 1 (by decide),
    source_yRow_eq_rowCompute 23 1 15 2 (by decide),
    source_yRow_eq_rowCompute 23 1 15 3 (by decide),
    source_yRow_eq_rowCompute 23 1 15 4 (by decide),
    source_yRow_eq_rowCompute 23 1 15 5 (by decide),
    source_yRow_eq_rowCompute 23 1 15 6 (by decide),
    computeRow_23_1_15_0, computeRow_23_1_15_1, computeRow_23_1_15_2, computeRow_23_1_15_3, computeRow_23_1_15_4, computeRow_23_1_15_5, computeRow_23_1_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_17 : Y 23 1 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 17 0 (by decide),
    source_yRow_eq_rowCompute 23 1 17 1 (by decide),
    source_yRow_eq_rowCompute 23 1 17 2 (by decide),
    source_yRow_eq_rowCompute 23 1 17 3 (by decide),
    source_yRow_eq_rowCompute 23 1 17 4 (by decide),
    source_yRow_eq_rowCompute 23 1 17 5 (by decide),
    source_yRow_eq_rowCompute 23 1 17 6 (by decide),
    computeRow_23_1_17_0, computeRow_23_1_17_1, computeRow_23_1_17_2, computeRow_23_1_17_3, computeRow_23_1_17_4, computeRow_23_1_17_5, computeRow_23_1_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_19 : Y 23 1 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 19 0 (by decide),
    source_yRow_eq_rowCompute 23 1 19 1 (by decide),
    source_yRow_eq_rowCompute 23 1 19 2 (by decide),
    source_yRow_eq_rowCompute 23 1 19 3 (by decide),
    source_yRow_eq_rowCompute 23 1 19 4 (by decide),
    source_yRow_eq_rowCompute 23 1 19 5 (by decide),
    source_yRow_eq_rowCompute 23 1 19 6 (by decide),
    computeRow_23_1_19_0, computeRow_23_1_19_1, computeRow_23_1_19_2, computeRow_23_1_19_3, computeRow_23_1_19_4, computeRow_23_1_19_5, computeRow_23_1_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_21 : Y 23 1 21 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 21 0 (by decide),
    source_yRow_eq_rowCompute 23 1 21 1 (by decide),
    source_yRow_eq_rowCompute 23 1 21 2 (by decide),
    source_yRow_eq_rowCompute 23 1 21 3 (by decide),
    source_yRow_eq_rowCompute 23 1 21 4 (by decide),
    source_yRow_eq_rowCompute 23 1 21 5 (by decide),
    source_yRow_eq_rowCompute 23 1 21 6 (by decide),
    computeRow_23_1_21_0, computeRow_23_1_21_1, computeRow_23_1_21_2, computeRow_23_1_21_3, computeRow_23_1_21_4, computeRow_23_1_21_5, computeRow_23_1_21_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_1_23 : Y 23 1 23 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 1 23 0 (by decide),
    source_yRow_eq_rowCompute 23 1 23 1 (by decide),
    source_yRow_eq_rowCompute 23 1 23 2 (by decide),
    source_yRow_eq_rowCompute 23 1 23 3 (by decide),
    source_yRow_eq_rowCompute 23 1 23 4 (by decide),
    source_yRow_eq_rowCompute 23 1 23 5 (by decide),
    source_yRow_eq_rowCompute 23 1 23 6 (by decide),
    computeRow_23_1_23_0, computeRow_23_1_23_1, computeRow_23_1_23_2, computeRow_23_1_23_3, computeRow_23_1_23_4, computeRow_23_1_23_5, computeRow_23_1_23_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_3_3 : Y 23 3 3 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 3 3 0 (by decide),
    source_yRow_eq_rowCompute 23 3 3 1 (by decide),
    source_yRow_eq_rowCompute 23 3 3 2 (by decide),
    source_yRow_eq_rowCompute 23 3 3 3 (by decide),
    source_yRow_eq_rowCompute 23 3 3 4 (by decide),
    source_yRow_eq_rowCompute 23 3 3 5 (by decide),
    source_yRow_eq_rowCompute 23 3 3 6 (by decide),
    computeRow_23_3_3_0, computeRow_23_3_3_1, computeRow_23_3_3_2, computeRow_23_3_3_3, computeRow_23_3_3_4, computeRow_23_3_3_5, computeRow_23_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_3_5 : Y 23 3 5 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 3 5 0 (by decide),
    source_yRow_eq_rowCompute 23 3 5 1 (by decide),
    source_yRow_eq_rowCompute 23 3 5 2 (by decide),
    source_yRow_eq_rowCompute 23 3 5 3 (by decide),
    source_yRow_eq_rowCompute 23 3 5 4 (by decide),
    source_yRow_eq_rowCompute 23 3 5 5 (by decide),
    source_yRow_eq_rowCompute 23 3 5 6 (by decide),
    computeRow_23_3_5_0, computeRow_23_3_5_1, computeRow_23_3_5_2, computeRow_23_3_5_3, computeRow_23_3_5_4, computeRow_23_3_5_5, computeRow_23_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_3_7 : Y 23 3 7 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 3 7 0 (by decide),
    source_yRow_eq_rowCompute 23 3 7 1 (by decide),
    source_yRow_eq_rowCompute 23 3 7 2 (by decide),
    source_yRow_eq_rowCompute 23 3 7 3 (by decide),
    source_yRow_eq_rowCompute 23 3 7 4 (by decide),
    source_yRow_eq_rowCompute 23 3 7 5 (by decide),
    source_yRow_eq_rowCompute 23 3 7 6 (by decide),
    computeRow_23_3_7_0, computeRow_23_3_7_1, computeRow_23_3_7_2, computeRow_23_3_7_3, computeRow_23_3_7_4, computeRow_23_3_7_5, computeRow_23_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_3_9 : Y 23 3 9 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 3 9 0 (by decide),
    source_yRow_eq_rowCompute 23 3 9 1 (by decide),
    source_yRow_eq_rowCompute 23 3 9 2 (by decide),
    source_yRow_eq_rowCompute 23 3 9 3 (by decide),
    source_yRow_eq_rowCompute 23 3 9 4 (by decide),
    source_yRow_eq_rowCompute 23 3 9 5 (by decide),
    source_yRow_eq_rowCompute 23 3 9 6 (by decide),
    computeRow_23_3_9_0, computeRow_23_3_9_1, computeRow_23_3_9_2, computeRow_23_3_9_3, computeRow_23_3_9_4, computeRow_23_3_9_5, computeRow_23_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_3_11 : Y 23 3 11 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 3 11 0 (by decide),
    source_yRow_eq_rowCompute 23 3 11 1 (by decide),
    source_yRow_eq_rowCompute 23 3 11 2 (by decide),
    source_yRow_eq_rowCompute 23 3 11 3 (by decide),
    source_yRow_eq_rowCompute 23 3 11 4 (by decide),
    source_yRow_eq_rowCompute 23 3 11 5 (by decide),
    source_yRow_eq_rowCompute 23 3 11 6 (by decide),
    computeRow_23_3_11_0, computeRow_23_3_11_1, computeRow_23_3_11_2, computeRow_23_3_11_3, computeRow_23_3_11_4, computeRow_23_3_11_5, computeRow_23_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_3_13 : Y 23 3 13 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 3 13 0 (by decide),
    source_yRow_eq_rowCompute 23 3 13 1 (by decide),
    source_yRow_eq_rowCompute 23 3 13 2 (by decide),
    source_yRow_eq_rowCompute 23 3 13 3 (by decide),
    source_yRow_eq_rowCompute 23 3 13 4 (by decide),
    source_yRow_eq_rowCompute 23 3 13 5 (by decide),
    source_yRow_eq_rowCompute 23 3 13 6 (by decide),
    computeRow_23_3_13_0, computeRow_23_3_13_1, computeRow_23_3_13_2, computeRow_23_3_13_3, computeRow_23_3_13_4, computeRow_23_3_13_5, computeRow_23_3_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_3_15 : Y 23 3 15 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 3 15 0 (by decide),
    source_yRow_eq_rowCompute 23 3 15 1 (by decide),
    source_yRow_eq_rowCompute 23 3 15 2 (by decide),
    source_yRow_eq_rowCompute 23 3 15 3 (by decide),
    source_yRow_eq_rowCompute 23 3 15 4 (by decide),
    source_yRow_eq_rowCompute 23 3 15 5 (by decide),
    source_yRow_eq_rowCompute 23 3 15 6 (by decide),
    computeRow_23_3_15_0, computeRow_23_3_15_1, computeRow_23_3_15_2, computeRow_23_3_15_3, computeRow_23_3_15_4, computeRow_23_3_15_5, computeRow_23_3_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_3_17 : Y 23 3 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 3 17 0 (by decide),
    source_yRow_eq_rowCompute 23 3 17 1 (by decide),
    source_yRow_eq_rowCompute 23 3 17 2 (by decide),
    source_yRow_eq_rowCompute 23 3 17 3 (by decide),
    source_yRow_eq_rowCompute 23 3 17 4 (by decide),
    source_yRow_eq_rowCompute 23 3 17 5 (by decide),
    source_yRow_eq_rowCompute 23 3 17 6 (by decide),
    computeRow_23_3_17_0, computeRow_23_3_17_1, computeRow_23_3_17_2, computeRow_23_3_17_3, computeRow_23_3_17_4, computeRow_23_3_17_5, computeRow_23_3_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_5_5 : Y 23 5 5 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 5 5 0 (by decide),
    source_yRow_eq_rowCompute 23 5 5 1 (by decide),
    source_yRow_eq_rowCompute 23 5 5 2 (by decide),
    source_yRow_eq_rowCompute 23 5 5 3 (by decide),
    source_yRow_eq_rowCompute 23 5 5 4 (by decide),
    source_yRow_eq_rowCompute 23 5 5 5 (by decide),
    source_yRow_eq_rowCompute 23 5 5 6 (by decide),
    computeRow_23_5_5_0, computeRow_23_5_5_1, computeRow_23_5_5_2, computeRow_23_5_5_3, computeRow_23_5_5_4, computeRow_23_5_5_5, computeRow_23_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_5_7 : Y 23 5 7 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 5 7 0 (by decide),
    source_yRow_eq_rowCompute 23 5 7 1 (by decide),
    source_yRow_eq_rowCompute 23 5 7 2 (by decide),
    source_yRow_eq_rowCompute 23 5 7 3 (by decide),
    source_yRow_eq_rowCompute 23 5 7 4 (by decide),
    source_yRow_eq_rowCompute 23 5 7 5 (by decide),
    source_yRow_eq_rowCompute 23 5 7 6 (by decide),
    computeRow_23_5_7_0, computeRow_23_5_7_1, computeRow_23_5_7_2, computeRow_23_5_7_3, computeRow_23_5_7_4, computeRow_23_5_7_5, computeRow_23_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_5_9 : Y 23 5 9 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 5 9 0 (by decide),
    source_yRow_eq_rowCompute 23 5 9 1 (by decide),
    source_yRow_eq_rowCompute 23 5 9 2 (by decide),
    source_yRow_eq_rowCompute 23 5 9 3 (by decide),
    source_yRow_eq_rowCompute 23 5 9 4 (by decide),
    source_yRow_eq_rowCompute 23 5 9 5 (by decide),
    source_yRow_eq_rowCompute 23 5 9 6 (by decide),
    computeRow_23_5_9_0, computeRow_23_5_9_1, computeRow_23_5_9_2, computeRow_23_5_9_3, computeRow_23_5_9_4, computeRow_23_5_9_5, computeRow_23_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_7_7 : Y 23 7 7 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 7 7 0 (by decide),
    source_yRow_eq_rowCompute 23 7 7 1 (by decide),
    source_yRow_eq_rowCompute 23 7 7 2 (by decide),
    source_yRow_eq_rowCompute 23 7 7 3 (by decide),
    source_yRow_eq_rowCompute 23 7 7 4 (by decide),
    source_yRow_eq_rowCompute 23 7 7 5 (by decide),
    source_yRow_eq_rowCompute 23 7 7 6 (by decide),
    computeRow_23_7_7_0, computeRow_23_7_7_1, computeRow_23_7_7_2, computeRow_23_7_7_3, computeRow_23_7_7_4, computeRow_23_7_7_5, computeRow_23_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_7_9 : Y 23 7 9 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 7 9 0 (by decide),
    source_yRow_eq_rowCompute 23 7 9 1 (by decide),
    source_yRow_eq_rowCompute 23 7 9 2 (by decide),
    source_yRow_eq_rowCompute 23 7 9 3 (by decide),
    source_yRow_eq_rowCompute 23 7 9 4 (by decide),
    source_yRow_eq_rowCompute 23 7 9 5 (by decide),
    source_yRow_eq_rowCompute 23 7 9 6 (by decide),
    computeRow_23_7_9_0, computeRow_23_7_9_1, computeRow_23_7_9_2, computeRow_23_7_9_3, computeRow_23_7_9_4, computeRow_23_7_9_5, computeRow_23_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_23_9_9 : Y 23 9 9 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 23 9 9 0 (by decide),
    source_yRow_eq_rowCompute 23 9 9 1 (by decide),
    source_yRow_eq_rowCompute 23 9 9 2 (by decide),
    source_yRow_eq_rowCompute 23 9 9 3 (by decide),
    source_yRow_eq_rowCompute 23 9 9 4 (by decide),
    source_yRow_eq_rowCompute 23 9 9 5 (by decide),
    source_yRow_eq_rowCompute 23 9 9 6 (by decide),
    computeRow_23_9_9_0, computeRow_23_9_9_1, computeRow_23_9_9_2, computeRow_23_9_9_3, computeRow_23_9_9_4, computeRow_23_9_9_5, computeRow_23_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem error_23_oai : errorRational 23 = candidateY_23 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_23_1_1
  · exact source_error_23_1_3
  · exact source_error_23_1_5
  · exact source_error_23_1_7
  · exact source_error_23_1_9
  · exact source_error_23_1_11
  · exact source_error_23_1_13
  · exact source_error_23_1_15
  · exact source_error_23_1_17
  · exact source_error_23_1_19
  · exact source_error_23_1_21
  · exact source_error_23_1_23
  · exact source_error_23_3_1
  · exact source_error_23_3_3
  · exact source_error_23_3_5
  · exact source_error_23_3_7
  · exact source_error_23_3_9
  · exact source_error_23_3_11
  · exact source_error_23_3_13
  · exact source_error_23_3_15
  · exact source_error_23_3_17
  · exact source_error_23_3_19
  · exact source_error_23_3_21
  · exact source_error_23_3_23
  · exact source_error_23_5_1
  · exact source_error_23_5_3
  · exact source_error_23_5_5
  · exact source_error_23_5_7
  · exact source_error_23_5_9
  · exact source_error_23_5_11
  · exact source_error_23_5_13
  · exact source_error_23_5_15
  · exact source_error_23_5_17
  · exact source_error_23_5_19
  · exact source_error_23_5_21
  · exact source_error_23_5_23
  · exact source_error_23_7_1
  · exact source_error_23_7_3
  · exact source_error_23_7_5
  · exact source_error_23_7_7
  · exact source_error_23_7_9
  · exact source_error_23_7_11
  · exact source_error_23_7_13
  · exact source_error_23_7_15
  · exact source_error_23_7_17
  · exact source_error_23_7_19
  · exact source_error_23_7_21
  · exact source_error_23_7_23
  · exact source_error_23_9_1
  · exact source_error_23_9_3
  · exact source_error_23_9_5
  · exact source_error_23_9_7
  · exact source_error_23_9_9
  · exact source_error_23_9_11
  · exact source_error_23_9_13
  · exact source_error_23_9_15
  · exact source_error_23_9_17
  · exact source_error_23_9_19
  · exact source_error_23_9_21
  · exact source_error_23_9_23
  · exact source_error_23_11_1
  · exact source_error_23_11_3
  · exact source_error_23_11_5
  · exact source_error_23_11_7
  · exact source_error_23_11_9
  · exact source_error_23_11_11
  · exact source_error_23_11_13
  · exact source_error_23_11_15
  · exact source_error_23_11_17
  · exact source_error_23_11_19
  · exact source_error_23_11_21
  · exact source_error_23_11_23
  · exact source_error_23_13_1
  · exact source_error_23_13_3
  · exact source_error_23_13_5
  · exact source_error_23_13_7
  · exact source_error_23_13_9
  · exact source_error_23_13_11
  · exact source_error_23_13_13
  · exact source_error_23_13_15
  · exact source_error_23_13_17
  · exact source_error_23_13_19
  · exact source_error_23_13_21
  · exact source_error_23_13_23
  · exact source_error_23_15_1
  · exact source_error_23_15_3
  · exact source_error_23_15_5
  · exact source_error_23_15_7
  · exact source_error_23_15_9
  · exact source_error_23_15_11
  · exact source_error_23_15_13
  · exact source_error_23_15_15
  · exact source_error_23_15_17
  · exact source_error_23_15_19
  · exact source_error_23_15_21
  · exact source_error_23_15_23
  · exact source_error_23_17_1
  · exact source_error_23_17_3
  · exact source_error_23_17_5
  · exact source_error_23_17_7
  · exact source_error_23_17_9
  · exact source_error_23_17_11
  · exact source_error_23_17_13
  · exact source_error_23_17_15
  · exact source_error_23_17_17
  · exact source_error_23_17_19
  · exact source_error_23_17_21
  · exact source_error_23_17_23
  · exact source_error_23_19_1
  · exact source_error_23_19_3
  · exact source_error_23_19_5
  · exact source_error_23_19_7
  · exact source_error_23_19_9
  · exact source_error_23_19_11
  · exact source_error_23_19_13
  · exact source_error_23_19_15
  · exact source_error_23_19_17
  · exact source_error_23_19_19
  · exact source_error_23_19_21
  · exact source_error_23_19_23
  · exact source_error_23_21_1
  · exact source_error_23_21_3
  · exact source_error_23_21_5
  · exact source_error_23_21_7
  · exact source_error_23_21_9
  · exact source_error_23_21_11
  · exact source_error_23_21_13
  · exact source_error_23_21_15
  · exact source_error_23_21_17
  · exact source_error_23_21_19
  · exact source_error_23_21_21
  · exact source_error_23_21_23
  · exact source_error_23_23_1
  · exact source_error_23_23_3
  · exact source_error_23_23_5
  · exact source_error_23_23_7
  · exact source_error_23_23_9
  · exact source_error_23_23_11
  · exact source_error_23_23_13
  · exact source_error_23_23_15
  · exact source_error_23_23_17
  · exact source_error_23_23_19
  · exact source_error_23_23_21
  · exact source_error_23_23_23

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_23_oai := @OAI.Laughlin.Certificate.error_23_oai
