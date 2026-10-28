-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T08:59:39.064733+00:00
-- url     : https://prove2.me/submissions/4d34b3d9-0a28-450e-8261-66b08bb197ce

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_7

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0107Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_1_7_0 : RowCompute.yRowIntegralFast 19 1 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_7_1 : RowCompute.yRowIntegralFast 19 1 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_7_2 : RowCompute.yRowIntegralFast 19 1 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_7_3 : RowCompute.yRowIntegralFast 19 1 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_7_4 : RowCompute.yRowIntegralFast 19 1 7 (RowCompute.rows[4]!) =
    (-26972334145563361686531687822145599384256441675848320286720000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_7_5 : RowCompute.yRowIntegralFast 19 1 7 (RowCompute.rows[5]!) =
    (37004774860555819092072401699326115189224813783339203821568000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_7_6 : RowCompute.yRowIntegralFast 19 1 7 (RowCompute.rows[6]!) =
    (-14061833869600395186164111068403207362467023135526107480064000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0109Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_1_9_0 : RowCompute.yRowIntegralFast 19 1 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_9_1 : RowCompute.yRowIntegralFast 19 1 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_9_2 : RowCompute.yRowIntegralFast 19 1 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_9_3 : RowCompute.yRowIntegralFast 19 1 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_9_4 : RowCompute.yRowIntegralFast 19 1 9 (RowCompute.rows[4]!) =
    (23609167210311475829218677400446440915117310376676138837606400000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_9_5 : RowCompute.yRowIntegralFast 19 1 9 (RowCompute.rows[5]!) =
    (-31490512481257584778801549914352591465095216495743559794688000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_9_6 : RowCompute.yRowIntegralFast 19 1 9 (RowCompute.rows[6]!) =
    (9084433520965899518978901116155041330045704786023734784819200000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0117Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_1_17_0 : RowCompute.yRowIntegralFast 19 1 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_17_1 : RowCompute.yRowIntegralFast 19 1 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_17_2 : RowCompute.yRowIntegralFast 19 1 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_17_3 : RowCompute.yRowIntegralFast 19 1 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_17_4 : RowCompute.yRowIntegralFast 19 1 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_17_5 : RowCompute.yRowIntegralFast 19 1 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_17_6 : RowCompute.yRowIntegralFast 19 1 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0119Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_1_19_0 : RowCompute.yRowIntegralFast 19 1 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_19_1 : RowCompute.yRowIntegralFast 19 1 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_19_2 : RowCompute.yRowIntegralFast 19 1 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_19_3 : RowCompute.yRowIntegralFast 19 1 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_19_4 : RowCompute.yRowIntegralFast 19 1 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_19_5 : RowCompute.yRowIntegralFast 19 1 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_1_19_6 : RowCompute.yRowIntegralFast 19 1 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0309Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_3_9_0 : RowCompute.yRowIntegralFast 19 3 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_9_1 : RowCompute.yRowIntegralFast 19 3 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_9_2 : RowCompute.yRowIntegralFast 19 3 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_9_3 : RowCompute.yRowIntegralFast 19 3 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_9_4 : RowCompute.yRowIntegralFast 19 3 9 (RowCompute.rows[4]!) =
    (-3697551319223915120295520441828708267741486020803899372339200000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_9_5 : RowCompute.yRowIntegralFast 19 3 9 (RowCompute.rows[5]!) =
    (4152296979097827436672244671313362365459265680443167683379200000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_9_6 : RowCompute.yRowIntegralFast 19 3 9 (RowCompute.rows[6]!) =
    (-851260716640303522060242217481606431699598662325002410393600000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0317Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_3_17_0 : RowCompute.yRowIntegralFast 19 3 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_17_1 : RowCompute.yRowIntegralFast 19 3 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_17_2 : RowCompute.yRowIntegralFast 19 3 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_17_3 : RowCompute.yRowIntegralFast 19 3 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_17_4 : RowCompute.yRowIntegralFast 19 3 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_17_5 : RowCompute.yRowIntegralFast 19 3 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_17_6 : RowCompute.yRowIntegralFast 19 3 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0319Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_3_19_0 : RowCompute.yRowIntegralFast 19 3 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_19_1 : RowCompute.yRowIntegralFast 19 3 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_19_2 : RowCompute.yRowIntegralFast 19 3 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_19_3 : RowCompute.yRowIntegralFast 19 3 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_19_4 : RowCompute.yRowIntegralFast 19 3 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_19_5 : RowCompute.yRowIntegralFast 19 3 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_3_19_6 : RowCompute.yRowIntegralFast 19 3 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0507Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_5_7_0 : RowCompute.yRowIntegralFast 19 5 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_7_1 : RowCompute.yRowIntegralFast 19 5 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_7_2 : RowCompute.yRowIntegralFast 19 5 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_7_3 : RowCompute.yRowIntegralFast 19 5 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_7_4 : RowCompute.yRowIntegralFast 19 5 7 (RowCompute.rows[4]!) =
    (-1668169038732285024004667245023978304871102683399285899264000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_7_5 : RowCompute.yRowIntegralFast 19 5 7 (RowCompute.rows[5]!) =
    (967362257181728666059542683436527318688372157908114210816000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_7_6 : RowCompute.yRowIntegralFast 19 5 7 (RowCompute.rows[6]!) =
    (194409924551714534318049555533647708000204680634263876403200000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0517Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_5_17_0 : RowCompute.yRowIntegralFast 19 5 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_17_1 : RowCompute.yRowIntegralFast 19 5 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_17_2 : RowCompute.yRowIntegralFast 19 5 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_17_3 : RowCompute.yRowIntegralFast 19 5 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_17_4 : RowCompute.yRowIntegralFast 19 5 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_17_5 : RowCompute.yRowIntegralFast 19 5 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_17_6 : RowCompute.yRowIntegralFast 19 5 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0519Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_5_19_0 : RowCompute.yRowIntegralFast 19 5 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_19_1 : RowCompute.yRowIntegralFast 19 5 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_19_2 : RowCompute.yRowIntegralFast 19 5 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_19_3 : RowCompute.yRowIntegralFast 19 5 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_19_4 : RowCompute.yRowIntegralFast 19 5 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_19_5 : RowCompute.yRowIntegralFast 19 5 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_5_19_6 : RowCompute.yRowIntegralFast 19 5 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0707Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_7_7_0 : RowCompute.yRowIntegralFast 19 7 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_7_1 : RowCompute.yRowIntegralFast 19 7 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_7_2 : RowCompute.yRowIntegralFast 19 7 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_7_3 : RowCompute.yRowIntegralFast 19 7 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_7_4 : RowCompute.yRowIntegralFast 19 7 7 (RowCompute.rows[4]!) =
    (701615787919667393603024137466614005569161804719077720064000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_7_5 : RowCompute.yRowIntegralFast 19 7 7 (RowCompute.rows[5]!) =
    (-154330591396238772524570528823688272974061622842403848192000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_7_6 : RowCompute.yRowIntegralFast 19 7 7 (RowCompute.rows[6]!) =
    (-219138954264305928107196033536049245875603889207975608320000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0709Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_7_9_0 : RowCompute.yRowIntegralFast 19 7 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_9_1 : RowCompute.yRowIntegralFast 19 7 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_9_2 : RowCompute.yRowIntegralFast 19 7 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_9_3 : RowCompute.yRowIntegralFast 19 7 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_9_4 : RowCompute.yRowIntegralFast 19 7 9 (RowCompute.rows[4]!) =
    (-330565319280558654191172511314929883286372351281532502016000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_9_5 : RowCompute.yRowIntegralFast 19 7 9 (RowCompute.rows[5]!) =
    (483490201531805346786775212896024930035815138094743552000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_9_6 : RowCompute.yRowIntegralFast 19 7 9 (RowCompute.rows[6]!) =
    (51973725287440139371612404990492101994492706414462500864000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0717Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_7_17_0 : RowCompute.yRowIntegralFast 19 7 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_17_1 : RowCompute.yRowIntegralFast 19 7 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_17_2 : RowCompute.yRowIntegralFast 19 7 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_17_3 : RowCompute.yRowIntegralFast 19 7 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_17_4 : RowCompute.yRowIntegralFast 19 7 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_17_5 : RowCompute.yRowIntegralFast 19 7 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_17_6 : RowCompute.yRowIntegralFast 19 7 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0719Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_7_19_0 : RowCompute.yRowIntegralFast 19 7 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_19_1 : RowCompute.yRowIntegralFast 19 7 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_19_2 : RowCompute.yRowIntegralFast 19 7 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_19_3 : RowCompute.yRowIntegralFast 19 7 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_19_4 : RowCompute.yRowIntegralFast 19 7 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_19_5 : RowCompute.yRowIntegralFast 19 7 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_7_19_6 : RowCompute.yRowIntegralFast 19 7 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0909Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_9_9_0 : RowCompute.yRowIntegralFast 19 9 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_9_1 : RowCompute.yRowIntegralFast 19 9 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_9_2 : RowCompute.yRowIntegralFast 19 9 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_9_3 : RowCompute.yRowIntegralFast 19 9 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_9_4 : RowCompute.yRowIntegralFast 19 9 9 (RowCompute.rows[4]!) =
    (182681746526119350112452975959508424858110438941908795392000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_9_5 : RowCompute.yRowIntegralFast 19 9 9 (RowCompute.rows[5]!) =
    (147313258098865979349329379390205179834722916061453221888000000000 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_9_6 : RowCompute.yRowIntegralFast 19 9 9 (RowCompute.rows[6]!) =
    (4169685946176150785735455498132076735912276154472464384000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0917Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_9_17_0 : RowCompute.yRowIntegralFast 19 9 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_17_1 : RowCompute.yRowIntegralFast 19 9 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_17_2 : RowCompute.yRowIntegralFast 19 9 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_17_3 : RowCompute.yRowIntegralFast 19 9 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_17_4 : RowCompute.yRowIntegralFast 19 9 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_17_5 : RowCompute.yRowIntegralFast 19 9 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_17_6 : RowCompute.yRowIntegralFast 19 9 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0919Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_9_19_0 : RowCompute.yRowIntegralFast 19 9 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_19_1 : RowCompute.yRowIntegralFast 19 9 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_19_2 : RowCompute.yRowIntegralFast 19 9 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_19_3 : RowCompute.yRowIntegralFast 19 9 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_19_4 : RowCompute.yRowIntegralFast 19 9 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_19_5 : RowCompute.yRowIntegralFast 19 9 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_9_19_6 : RowCompute.yRowIntegralFast 19 9 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1117Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_11_17_0 : RowCompute.yRowIntegralFast 19 11 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_17_1 : RowCompute.yRowIntegralFast 19 11 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_17_2 : RowCompute.yRowIntegralFast 19 11 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_17_3 : RowCompute.yRowIntegralFast 19 11 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_17_4 : RowCompute.yRowIntegralFast 19 11 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_17_5 : RowCompute.yRowIntegralFast 19 11 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_17_6 : RowCompute.yRowIntegralFast 19 11 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1119Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_11_19_0 : RowCompute.yRowIntegralFast 19 11 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_19_1 : RowCompute.yRowIntegralFast 19 11 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_19_2 : RowCompute.yRowIntegralFast 19 11 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_19_3 : RowCompute.yRowIntegralFast 19 11 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_19_4 : RowCompute.yRowIntegralFast 19 11 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_19_5 : RowCompute.yRowIntegralFast 19 11 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_11_19_6 : RowCompute.yRowIntegralFast 19 11 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1317Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_13_17_0 : RowCompute.yRowIntegralFast 19 13 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_17_1 : RowCompute.yRowIntegralFast 19 13 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_17_2 : RowCompute.yRowIntegralFast 19 13 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_17_3 : RowCompute.yRowIntegralFast 19 13 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_17_4 : RowCompute.yRowIntegralFast 19 13 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_17_5 : RowCompute.yRowIntegralFast 19 13 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_17_6 : RowCompute.yRowIntegralFast 19 13 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1319Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_13_19_0 : RowCompute.yRowIntegralFast 19 13 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_19_1 : RowCompute.yRowIntegralFast 19 13 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_19_2 : RowCompute.yRowIntegralFast 19 13 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_19_3 : RowCompute.yRowIntegralFast 19 13 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_19_4 : RowCompute.yRowIntegralFast 19 13 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_19_5 : RowCompute.yRowIntegralFast 19 13 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_13_19_6 : RowCompute.yRowIntegralFast 19 13 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1517Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_15_17_0 : RowCompute.yRowIntegralFast 19 15 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_17_1 : RowCompute.yRowIntegralFast 19 15 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_17_2 : RowCompute.yRowIntegralFast 19 15 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_17_3 : RowCompute.yRowIntegralFast 19 15 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_17_4 : RowCompute.yRowIntegralFast 19 15 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_17_5 : RowCompute.yRowIntegralFast 19 15 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_17_6 : RowCompute.yRowIntegralFast 19 15 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1519Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_15_19_0 : RowCompute.yRowIntegralFast 19 15 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_19_1 : RowCompute.yRowIntegralFast 19 15 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_19_2 : RowCompute.yRowIntegralFast 19 15 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_19_3 : RowCompute.yRowIntegralFast 19 15 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_19_4 : RowCompute.yRowIntegralFast 19 15 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_19_5 : RowCompute.yRowIntegralFast 19 15 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_15_19_6 : RowCompute.yRowIntegralFast 19 15 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1717Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_17_17_0 : RowCompute.yRowIntegralFast 19 17 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_17_1 : RowCompute.yRowIntegralFast 19 17 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_17_2 : RowCompute.yRowIntegralFast 19 17 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_17_3 : RowCompute.yRowIntegralFast 19 17 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_17_4 : RowCompute.yRowIntegralFast 19 17 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_17_5 : RowCompute.yRowIntegralFast 19 17 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_17_6 : RowCompute.yRowIntegralFast 19 17 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1719Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_17_19_0 : RowCompute.yRowIntegralFast 19 17 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_19_1 : RowCompute.yRowIntegralFast 19 17 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_19_2 : RowCompute.yRowIntegralFast 19 17 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_19_3 : RowCompute.yRowIntegralFast 19 17 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_19_4 : RowCompute.yRowIntegralFast 19 17 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_19_5 : RowCompute.yRowIntegralFast 19 17 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_17_19_6 : RowCompute.yRowIntegralFast 19 17 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1919Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_19_19_19_0 : RowCompute.yRowIntegralFast 19 19 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_19_19_1 : RowCompute.yRowIntegralFast 19 19 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_19_19_2 : RowCompute.yRowIntegralFast 19 19 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_19_19_3 : RowCompute.yRowIntegralFast 19 19 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_19_19_4 : RowCompute.yRowIntegralFast 19 19 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_19_19_5 : RowCompute.yRowIntegralFast 19 19 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_19_19_19_6 : RowCompute.yRowIntegralFast 19 19 19 (RowCompute.rows[6]!) =
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_19_1_7 : Y 19 1 7 = (14766383937965483058974739/4194304000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 1 7 0 (by decide),
    source_yRow_eq_rowCompute 19 1 7 1 (by decide),
    source_yRow_eq_rowCompute 19 1 7 2 (by decide),
    source_yRow_eq_rowCompute 19 1 7 3 (by decide),
    source_yRow_eq_rowCompute 19 1 7 4 (by decide),
    source_yRow_eq_rowCompute 19 1 7 5 (by decide),
    source_yRow_eq_rowCompute 19 1 7 6 (by decide),
    computeRow_19_1_7_0, computeRow_19_1_7_1, computeRow_19_1_7_2, computeRow_19_1_7_3, computeRow_19_1_7_4, computeRow_19_1_7_5, computeRow_19_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_1_9 : Y 19 1 9 = (-5511147190592216732622063/5242880000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 1 9 0 (by decide),
    source_yRow_eq_rowCompute 19 1 9 1 (by decide),
    source_yRow_eq_rowCompute 19 1 9 2 (by decide),
    source_yRow_eq_rowCompute 19 1 9 3 (by decide),
    source_yRow_eq_rowCompute 19 1 9 4 (by decide),
    source_yRow_eq_rowCompute 19 1 9 5 (by decide),
    source_yRow_eq_rowCompute 19 1 9 6 (by decide),
    computeRow_19_1_9_0, computeRow_19_1_9_1, computeRow_19_1_9_2, computeRow_19_1_9_3, computeRow_19_1_9_4, computeRow_19_1_9_5, computeRow_19_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_1_17 : Y 19 1 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 1 17 0 (by decide),
    source_yRow_eq_rowCompute 19 1 17 1 (by decide),
    source_yRow_eq_rowCompute 19 1 17 2 (by decide),
    source_yRow_eq_rowCompute 19 1 17 3 (by decide),
    source_yRow_eq_rowCompute 19 1 17 4 (by decide),
    source_yRow_eq_rowCompute 19 1 17 5 (by decide),
    source_yRow_eq_rowCompute 19 1 17 6 (by decide),
    computeRow_19_1_17_0, computeRow_19_1_17_1, computeRow_19_1_17_2, computeRow_19_1_17_3, computeRow_19_1_17_4, computeRow_19_1_17_5, computeRow_19_1_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_1_19 : Y 19 1 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 1 19 0 (by decide),
    source_yRow_eq_rowCompute 19 1 19 1 (by decide),
    source_yRow_eq_rowCompute 19 1 19 2 (by decide),
    source_yRow_eq_rowCompute 19 1 19 3 (by decide),
    source_yRow_eq_rowCompute 19 1 19 4 (by decide),
    source_yRow_eq_rowCompute 19 1 19 5 (by decide),
    source_yRow_eq_rowCompute 19 1 19 6 (by decide),
    computeRow_19_1_19_0, computeRow_19_1_19_1, computeRow_19_1_19_2, computeRow_19_1_19_3, computeRow_19_1_19_4, computeRow_19_1_19_5, computeRow_19_1_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_3_9 : Y 19 3 9 = (908184765784913635277259/2621440000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 3 9 0 (by decide),
    source_yRow_eq_rowCompute 19 3 9 1 (by decide),
    source_yRow_eq_rowCompute 19 3 9 2 (by decide),
    source_yRow_eq_rowCompute 19 3 9 3 (by decide),
    source_yRow_eq_rowCompute 19 3 9 4 (by decide),
    source_yRow_eq_rowCompute 19 3 9 5 (by decide),
    source_yRow_eq_rowCompute 19 3 9 6 (by decide),
    computeRow_19_3_9_0, computeRow_19_3_9_1, computeRow_19_3_9_2, computeRow_19_3_9_3, computeRow_19_3_9_4, computeRow_19_3_9_5, computeRow_19_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_3_17 : Y 19 3 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 3 17 0 (by decide),
    source_yRow_eq_rowCompute 19 3 17 1 (by decide),
    source_yRow_eq_rowCompute 19 3 17 2 (by decide),
    source_yRow_eq_rowCompute 19 3 17 3 (by decide),
    source_yRow_eq_rowCompute 19 3 17 4 (by decide),
    source_yRow_eq_rowCompute 19 3 17 5 (by decide),
    source_yRow_eq_rowCompute 19 3 17 6 (by decide),
    computeRow_19_3_17_0, computeRow_19_3_17_1, computeRow_19_3_17_2, computeRow_19_3_17_3, computeRow_19_3_17_4, computeRow_19_3_17_5, computeRow_19_3_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_3_19 : Y 19 3 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 3 19 0 (by decide),
    source_yRow_eq_rowCompute 19 3 19 1 (by decide),
    source_yRow_eq_rowCompute 19 3 19 2 (by decide),
    source_yRow_eq_rowCompute 19 3 19 3 (by decide),
    source_yRow_eq_rowCompute 19 3 19 4 (by decide),
    source_yRow_eq_rowCompute 19 3 19 5 (by decide),
    source_yRow_eq_rowCompute 19 3 19 6 (by decide),
    computeRow_19_3_19_0, computeRow_19_3_19_1, computeRow_19_3_19_2, computeRow_19_3_19_3, computeRow_19_3_19_4, computeRow_19_3_19_5, computeRow_19_3_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_5_7 : Y 19 5 7 = (9278879137014220083120771/20971520000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 5 7 0 (by decide),
    source_yRow_eq_rowCompute 19 5 7 1 (by decide),
    source_yRow_eq_rowCompute 19 5 7 2 (by decide),
    source_yRow_eq_rowCompute 19 5 7 3 (by decide),
    source_yRow_eq_rowCompute 19 5 7 4 (by decide),
    source_yRow_eq_rowCompute 19 5 7 5 (by decide),
    source_yRow_eq_rowCompute 19 5 7 6 (by decide),
    computeRow_19_5_7_0, computeRow_19_5_7_1, computeRow_19_5_7_2, computeRow_19_5_7_3, computeRow_19_5_7_4, computeRow_19_5_7_5, computeRow_19_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_5_17 : Y 19 5 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 5 17 0 (by decide),
    source_yRow_eq_rowCompute 19 5 17 1 (by decide),
    source_yRow_eq_rowCompute 19 5 17 2 (by decide),
    source_yRow_eq_rowCompute 19 5 17 3 (by decide),
    source_yRow_eq_rowCompute 19 5 17 4 (by decide),
    source_yRow_eq_rowCompute 19 5 17 5 (by decide),
    source_yRow_eq_rowCompute 19 5 17 6 (by decide),
    computeRow_19_5_17_0, computeRow_19_5_17_1, computeRow_19_5_17_2, computeRow_19_5_17_3, computeRow_19_5_17_4, computeRow_19_5_17_5, computeRow_19_5_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_5_19 : Y 19 5 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 5 19 0 (by decide),
    source_yRow_eq_rowCompute 19 5 19 1 (by decide),
    source_yRow_eq_rowCompute 19 5 19 2 (by decide),
    source_yRow_eq_rowCompute 19 5 19 3 (by decide),
    source_yRow_eq_rowCompute 19 5 19 4 (by decide),
    source_yRow_eq_rowCompute 19 5 19 5 (by decide),
    source_yRow_eq_rowCompute 19 5 19 6 (by decide),
    computeRow_19_5_19_0, computeRow_19_5_19_1, computeRow_19_5_19_2, computeRow_19_5_19_3, computeRow_19_5_19_4, computeRow_19_5_19_5, computeRow_19_5_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_7_7 : Y 19 7 7 = (-601273345026853390678479/2097152000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 7 7 0 (by decide),
    source_yRow_eq_rowCompute 19 7 7 1 (by decide),
    source_yRow_eq_rowCompute 19 7 7 2 (by decide),
    source_yRow_eq_rowCompute 19 7 7 3 (by decide),
    source_yRow_eq_rowCompute 19 7 7 4 (by decide),
    source_yRow_eq_rowCompute 19 7 7 5 (by decide),
    source_yRow_eq_rowCompute 19 7 7 6 (by decide),
    computeRow_19_7_7_0, computeRow_19_7_7_1, computeRow_19_7_7_2, computeRow_19_7_7_3, computeRow_19_7_7_4, computeRow_19_7_7_5, computeRow_19_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_7_9 : Y 19 7 9 = (5095867887885096310527/20971520000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 7 9 0 (by decide),
    source_yRow_eq_rowCompute 19 7 9 1 (by decide),
    source_yRow_eq_rowCompute 19 7 9 2 (by decide),
    source_yRow_eq_rowCompute 19 7 9 3 (by decide),
    source_yRow_eq_rowCompute 19 7 9 4 (by decide),
    source_yRow_eq_rowCompute 19 7 9 5 (by decide),
    source_yRow_eq_rowCompute 19 7 9 6 (by decide),
    computeRow_19_7_9_0, computeRow_19_7_9_1, computeRow_19_7_9_2, computeRow_19_7_9_3, computeRow_19_7_9_4, computeRow_19_7_9_5, computeRow_19_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_7_17 : Y 19 7 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 7 17 0 (by decide),
    source_yRow_eq_rowCompute 19 7 17 1 (by decide),
    source_yRow_eq_rowCompute 19 7 17 2 (by decide),
    source_yRow_eq_rowCompute 19 7 17 3 (by decide),
    source_yRow_eq_rowCompute 19 7 17 4 (by decide),
    source_yRow_eq_rowCompute 19 7 17 5 (by decide),
    source_yRow_eq_rowCompute 19 7 17 6 (by decide),
    computeRow_19_7_17_0, computeRow_19_7_17_1, computeRow_19_7_17_2, computeRow_19_7_17_3, computeRow_19_7_17_4, computeRow_19_7_17_5, computeRow_19_7_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_7_19 : Y 19 7 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 7 19 0 (by decide),
    source_yRow_eq_rowCompute 19 7 19 1 (by decide),
    source_yRow_eq_rowCompute 19 7 19 2 (by decide),
    source_yRow_eq_rowCompute 19 7 19 3 (by decide),
    source_yRow_eq_rowCompute 19 7 19 4 (by decide),
    source_yRow_eq_rowCompute 19 7 19 5 (by decide),
    source_yRow_eq_rowCompute 19 7 19 6 (by decide),
    computeRow_19_7_19_0, computeRow_19_7_19_1, computeRow_19_7_19_2, computeRow_19_7_19_3, computeRow_19_7_19_4, computeRow_19_7_19_5, computeRow_19_7_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_9_9 : Y 19 9 9 = (-38268821834268590378583/131072000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 9 9 0 (by decide),
    source_yRow_eq_rowCompute 19 9 9 1 (by decide),
    source_yRow_eq_rowCompute 19 9 9 2 (by decide),
    source_yRow_eq_rowCompute 19 9 9 3 (by decide),
    source_yRow_eq_rowCompute 19 9 9 4 (by decide),
    source_yRow_eq_rowCompute 19 9 9 5 (by decide),
    source_yRow_eq_rowCompute 19 9 9 6 (by decide),
    computeRow_19_9_9_0, computeRow_19_9_9_1, computeRow_19_9_9_2, computeRow_19_9_9_3, computeRow_19_9_9_4, computeRow_19_9_9_5, computeRow_19_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_9_17 : Y 19 9 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 9 17 0 (by decide),
    source_yRow_eq_rowCompute 19 9 17 1 (by decide),
    source_yRow_eq_rowCompute 19 9 17 2 (by decide),
    source_yRow_eq_rowCompute 19 9 17 3 (by decide),
    source_yRow_eq_rowCompute 19 9 17 4 (by decide),
    source_yRow_eq_rowCompute 19 9 17 5 (by decide),
    source_yRow_eq_rowCompute 19 9 17 6 (by decide),
    computeRow_19_9_17_0, computeRow_19_9_17_1, computeRow_19_9_17_2, computeRow_19_9_17_3, computeRow_19_9_17_4, computeRow_19_9_17_5, computeRow_19_9_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_9_19 : Y 19 9 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 9 19 0 (by decide),
    source_yRow_eq_rowCompute 19 9 19 1 (by decide),
    source_yRow_eq_rowCompute 19 9 19 2 (by decide),
    source_yRow_eq_rowCompute 19 9 19 3 (by decide),
    source_yRow_eq_rowCompute 19 9 19 4 (by decide),
    source_yRow_eq_rowCompute 19 9 19 5 (by decide),
    source_yRow_eq_rowCompute 19 9 19 6 (by decide),
    computeRow_19_9_19_0, computeRow_19_9_19_1, computeRow_19_9_19_2, computeRow_19_9_19_3, computeRow_19_9_19_4, computeRow_19_9_19_5, computeRow_19_9_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_11_17 : Y 19 11 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 11 17 0 (by decide),
    source_yRow_eq_rowCompute 19 11 17 1 (by decide),
    source_yRow_eq_rowCompute 19 11 17 2 (by decide),
    source_yRow_eq_rowCompute 19 11 17 3 (by decide),
    source_yRow_eq_rowCompute 19 11 17 4 (by decide),
    source_yRow_eq_rowCompute 19 11 17 5 (by decide),
    source_yRow_eq_rowCompute 19 11 17 6 (by decide),
    computeRow_19_11_17_0, computeRow_19_11_17_1, computeRow_19_11_17_2, computeRow_19_11_17_3, computeRow_19_11_17_4, computeRow_19_11_17_5, computeRow_19_11_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_11_19 : Y 19 11 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 11 19 0 (by decide),
    source_yRow_eq_rowCompute 19 11 19 1 (by decide),
    source_yRow_eq_rowCompute 19 11 19 2 (by decide),
    source_yRow_eq_rowCompute 19 11 19 3 (by decide),
    source_yRow_eq_rowCompute 19 11 19 4 (by decide),
    source_yRow_eq_rowCompute 19 11 19 5 (by decide),
    source_yRow_eq_rowCompute 19 11 19 6 (by decide),
    computeRow_19_11_19_0, computeRow_19_11_19_1, computeRow_19_11_19_2, computeRow_19_11_19_3, computeRow_19_11_19_4, computeRow_19_11_19_5, computeRow_19_11_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_13_17 : Y 19 13 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 13 17 0 (by decide),
    source_yRow_eq_rowCompute 19 13 17 1 (by decide),
    source_yRow_eq_rowCompute 19 13 17 2 (by decide),
    source_yRow_eq_rowCompute 19 13 17 3 (by decide),
    source_yRow_eq_rowCompute 19 13 17 4 (by decide),
    source_yRow_eq_rowCompute 19 13 17 5 (by decide),
    source_yRow_eq_rowCompute 19 13 17 6 (by decide),
    computeRow_19_13_17_0, computeRow_19_13_17_1, computeRow_19_13_17_2, computeRow_19_13_17_3, computeRow_19_13_17_4, computeRow_19_13_17_5, computeRow_19_13_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_13_19 : Y 19 13 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 13 19 0 (by decide),
    source_yRow_eq_rowCompute 19 13 19 1 (by decide),
    source_yRow_eq_rowCompute 19 13 19 2 (by decide),
    source_yRow_eq_rowCompute 19 13 19 3 (by decide),
    source_yRow_eq_rowCompute 19 13 19 4 (by decide),
    source_yRow_eq_rowCompute 19 13 19 5 (by decide),
    source_yRow_eq_rowCompute 19 13 19 6 (by decide),
    computeRow_19_13_19_0, computeRow_19_13_19_1, computeRow_19_13_19_2, computeRow_19_13_19_3, computeRow_19_13_19_4, computeRow_19_13_19_5, computeRow_19_13_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_15_17 : Y 19 15 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 15 17 0 (by decide),
    source_yRow_eq_rowCompute 19 15 17 1 (by decide),
    source_yRow_eq_rowCompute 19 15 17 2 (by decide),
    source_yRow_eq_rowCompute 19 15 17 3 (by decide),
    source_yRow_eq_rowCompute 19 15 17 4 (by decide),
    source_yRow_eq_rowCompute 19 15 17 5 (by decide),
    source_yRow_eq_rowCompute 19 15 17 6 (by decide),
    computeRow_19_15_17_0, computeRow_19_15_17_1, computeRow_19_15_17_2, computeRow_19_15_17_3, computeRow_19_15_17_4, computeRow_19_15_17_5, computeRow_19_15_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_15_19 : Y 19 15 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 15 19 0 (by decide),
    source_yRow_eq_rowCompute 19 15 19 1 (by decide),
    source_yRow_eq_rowCompute 19 15 19 2 (by decide),
    source_yRow_eq_rowCompute 19 15 19 3 (by decide),
    source_yRow_eq_rowCompute 19 15 19 4 (by decide),
    source_yRow_eq_rowCompute 19 15 19 5 (by decide),
    source_yRow_eq_rowCompute 19 15 19 6 (by decide),
    computeRow_19_15_19_0, computeRow_19_15_19_1, computeRow_19_15_19_2, computeRow_19_15_19_3, computeRow_19_15_19_4, computeRow_19_15_19_5, computeRow_19_15_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_17_17 : Y 19 17 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 17 17 0 (by decide),
    source_yRow_eq_rowCompute 19 17 17 1 (by decide),
    source_yRow_eq_rowCompute 19 17 17 2 (by decide),
    source_yRow_eq_rowCompute 19 17 17 3 (by decide),
    source_yRow_eq_rowCompute 19 17 17 4 (by decide),
    source_yRow_eq_rowCompute 19 17 17 5 (by decide),
    source_yRow_eq_rowCompute 19 17 17 6 (by decide),
    computeRow_19_17_17_0, computeRow_19_17_17_1, computeRow_19_17_17_2, computeRow_19_17_17_3, computeRow_19_17_17_4, computeRow_19_17_17_5, computeRow_19_17_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_17_19 : Y 19 17 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 17 19 0 (by decide),
    source_yRow_eq_rowCompute 19 17 19 1 (by decide),
    source_yRow_eq_rowCompute 19 17 19 2 (by decide),
    source_yRow_eq_rowCompute 19 17 19 3 (by decide),
    source_yRow_eq_rowCompute 19 17 19 4 (by decide),
    source_yRow_eq_rowCompute 19 17 19 5 (by decide),
    source_yRow_eq_rowCompute 19 17 19 6 (by decide),
    computeRow_19_17_19_0, computeRow_19_17_19_1, computeRow_19_17_19_2, computeRow_19_17_19_3, computeRow_19_17_19_4, computeRow_19_17_19_5, computeRow_19_17_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_19_19_19 : Y 19 19 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 19 19 19 0 (by decide),
    source_yRow_eq_rowCompute 19 19 19 1 (by decide),
    source_yRow_eq_rowCompute 19 19 19 2 (by decide),
    source_yRow_eq_rowCompute 19 19 19 3 (by decide),
    source_yRow_eq_rowCompute 19 19 19 4 (by decide),
    source_yRow_eq_rowCompute 19 19 19 5 (by decide),
    source_yRow_eq_rowCompute 19 19 19 6 (by decide),
    computeRow_19_19_19_0, computeRow_19_19_19_1, computeRow_19_19_19_2, computeRow_19_19_19_3, computeRow_19_19_19_4, computeRow_19_19_19_5, computeRow_19_19_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem error_19_oai : errorRational 19 = candidateY_19 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_19_1_1
  · exact source_error_19_1_3
  · exact source_error_19_1_5
  · exact source_error_19_1_7
  · exact source_error_19_1_9
  · exact source_error_19_1_11
  · exact source_error_19_1_13
  · exact source_error_19_1_15
  · exact source_error_19_1_17
  · exact source_error_19_1_19
  · exact source_error_19_3_1
  · exact source_error_19_3_3
  · exact source_error_19_3_5
  · exact source_error_19_3_7
  · exact source_error_19_3_9
  · exact source_error_19_3_11
  · exact source_error_19_3_13
  · exact source_error_19_3_15
  · exact source_error_19_3_17
  · exact source_error_19_3_19
  · exact source_error_19_5_1
  · exact source_error_19_5_3
  · exact source_error_19_5_5
  · exact source_error_19_5_7
  · exact source_error_19_5_9
  · exact source_error_19_5_11
  · exact source_error_19_5_13
  · exact source_error_19_5_15
  · exact source_error_19_5_17
  · exact source_error_19_5_19
  · exact source_error_19_7_1
  · exact source_error_19_7_3
  · exact source_error_19_7_5
  · exact source_error_19_7_7
  · exact source_error_19_7_9
  · exact source_error_19_7_11
  · exact source_error_19_7_13
  · exact source_error_19_7_15
  · exact source_error_19_7_17
  · exact source_error_19_7_19
  · exact source_error_19_9_1
  · exact source_error_19_9_3
  · exact source_error_19_9_5
  · exact source_error_19_9_7
  · exact source_error_19_9_9
  · exact source_error_19_9_11
  · exact source_error_19_9_13
  · exact source_error_19_9_15
  · exact source_error_19_9_17
  · exact source_error_19_9_19
  · exact source_error_19_11_1
  · exact source_error_19_11_3
  · exact source_error_19_11_5
  · exact source_error_19_11_7
  · exact source_error_19_11_9
  · exact source_error_19_11_11
  · exact source_error_19_11_13
  · exact source_error_19_11_15
  · exact source_error_19_11_17
  · exact source_error_19_11_19
  · exact source_error_19_13_1
  · exact source_error_19_13_3
  · exact source_error_19_13_5
  · exact source_error_19_13_7
  · exact source_error_19_13_9
  · exact source_error_19_13_11
  · exact source_error_19_13_13
  · exact source_error_19_13_15
  · exact source_error_19_13_17
  · exact source_error_19_13_19
  · exact source_error_19_15_1
  · exact source_error_19_15_3
  · exact source_error_19_15_5
  · exact source_error_19_15_7
  · exact source_error_19_15_9
  · exact source_error_19_15_11
  · exact source_error_19_15_13
  · exact source_error_19_15_15
  · exact source_error_19_15_17
  · exact source_error_19_15_19
  · exact source_error_19_17_1
  · exact source_error_19_17_3
  · exact source_error_19_17_5
  · exact source_error_19_17_7
  · exact source_error_19_17_9
  · exact source_error_19_17_11
  · exact source_error_19_17_13
  · exact source_error_19_17_15
  · exact source_error_19_17_17
  · exact source_error_19_17_19
  · exact source_error_19_19_1
  · exact source_error_19_19_3
  · exact source_error_19_19_5
  · exact source_error_19_19_7
  · exact source_error_19_19_9
  · exact source_error_19_19_11
  · exact source_error_19_19_13
  · exact source_error_19_19_15
  · exact source_error_19_19_17
  · exact source_error_19_19_19

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_19_oai := @OAI.Laughlin.Certificate.error_19_oai
