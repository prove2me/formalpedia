-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_20
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:02:12.356239+00:00
-- url     : https://prove2.me/submissions/48cc8dda-6cfd-477c-9777-cd61d42ac330

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_7

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0107Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_1_7_0 : RowCompute.yRowIntegralFast 20 1 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_7_1 : RowCompute.yRowIntegralFast 20 1 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_7_2 : RowCompute.yRowIntegralFast 20 1 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_7_3 : RowCompute.yRowIntegralFast 20 1 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_7_4 : RowCompute.yRowIntegralFast 20 1 7 (RowCompute.rows[4]!) =
    (56975944322032423888819874699705961407574850209343573327872000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_7_5 : RowCompute.yRowIntegralFast 20 1 7 (RowCompute.rows[5]!) =
    (-63480216249207615117921098546445767210321011790814518024601600000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_7_6 : RowCompute.yRowIntegralFast 20 1 7 (RowCompute.rows[6]!) =
    (-12088023456763008476431120244899571637635076033884273718067200000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0117Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_1_17_0 : RowCompute.yRowIntegralFast 20 1 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_17_1 : RowCompute.yRowIntegralFast 20 1 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_17_2 : RowCompute.yRowIntegralFast 20 1 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_17_3 : RowCompute.yRowIntegralFast 20 1 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_17_4 : RowCompute.yRowIntegralFast 20 1 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_17_5 : RowCompute.yRowIntegralFast 20 1 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_17_6 : RowCompute.yRowIntegralFast 20 1 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0119Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_1_19_0 : RowCompute.yRowIntegralFast 20 1 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_19_1 : RowCompute.yRowIntegralFast 20 1 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_19_2 : RowCompute.yRowIntegralFast 20 1 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_19_3 : RowCompute.yRowIntegralFast 20 1 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_19_4 : RowCompute.yRowIntegralFast 20 1 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_19_5 : RowCompute.yRowIntegralFast 20 1 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_1_19_6 : RowCompute.yRowIntegralFast 20 1 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0309Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_3_9_0 : RowCompute.yRowIntegralFast 20 3 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_9_1 : RowCompute.yRowIntegralFast 20 3 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_9_2 : RowCompute.yRowIntegralFast 20 3 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_9_3 : RowCompute.yRowIntegralFast 20 3 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_9_4 : RowCompute.yRowIntegralFast 20 3 9 (RowCompute.rows[4]!) =
    (18878090156465950018570510575558293459587324182054077202432000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_9_5 : RowCompute.yRowIntegralFast 20 3 9 (RowCompute.rows[5]!) =
    (-1182260976868996701039821934691770612820582312702098643353600000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_9_6 : RowCompute.yRowIntegralFast 20 3 9 (RowCompute.rows[6]!) =
    (-21117530025230126032729417903315203603309828274829528137728000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0317Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_3_17_0 : RowCompute.yRowIntegralFast 20 3 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_17_1 : RowCompute.yRowIntegralFast 20 3 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_17_2 : RowCompute.yRowIntegralFast 20 3 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_17_3 : RowCompute.yRowIntegralFast 20 3 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_17_4 : RowCompute.yRowIntegralFast 20 3 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_17_5 : RowCompute.yRowIntegralFast 20 3 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_17_6 : RowCompute.yRowIntegralFast 20 3 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0319Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_3_19_0 : RowCompute.yRowIntegralFast 20 3 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_19_1 : RowCompute.yRowIntegralFast 20 3 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_19_2 : RowCompute.yRowIntegralFast 20 3 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_19_3 : RowCompute.yRowIntegralFast 20 3 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_19_4 : RowCompute.yRowIntegralFast 20 3 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_19_5 : RowCompute.yRowIntegralFast 20 3 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_3_19_6 : RowCompute.yRowIntegralFast 20 3 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0507Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_5_7_0 : RowCompute.yRowIntegralFast 20 5 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_7_1 : RowCompute.yRowIntegralFast 20 5 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_7_2 : RowCompute.yRowIntegralFast 20 5 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_7_3 : RowCompute.yRowIntegralFast 20 5 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_7_4 : RowCompute.yRowIntegralFast 20 5 7 (RowCompute.rows[4]!) =
    (1052025938690925032025211890678744261912594241113122930688000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_7_5 : RowCompute.yRowIntegralFast 20 5 7 (RowCompute.rows[5]!) =
    (-3840241209738055991411757429154362804461330159238069092352000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_7_6 : RowCompute.yRowIntegralFast 20 5 7 (RowCompute.rows[6]!) =
    (-623737020472807454924206410985530012261871828373801533440000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0509Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_5_9_0 : RowCompute.yRowIntegralFast 20 5 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_9_1 : RowCompute.yRowIntegralFast 20 5 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_9_2 : RowCompute.yRowIntegralFast 20 5 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_9_3 : RowCompute.yRowIntegralFast 20 5 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_9_4 : RowCompute.yRowIntegralFast 20 5 9 (RowCompute.rows[4]!) =
    (-2701811108122500610753084188044689412878171419362149269504000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_9_5 : RowCompute.yRowIntegralFast 20 5 9 (RowCompute.rows[5]!) =
    (368720202461155284386643423047943468815971794017989951488000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_9_6 : RowCompute.yRowIntegralFast 20 5 9 (RowCompute.rows[6]!) =
    (3989853386009315634527074649513016603409404394118766919680000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0517Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_5_17_0 : RowCompute.yRowIntegralFast 20 5 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_17_1 : RowCompute.yRowIntegralFast 20 5 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_17_2 : RowCompute.yRowIntegralFast 20 5 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_17_3 : RowCompute.yRowIntegralFast 20 5 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_17_4 : RowCompute.yRowIntegralFast 20 5 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_17_5 : RowCompute.yRowIntegralFast 20 5 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_17_6 : RowCompute.yRowIntegralFast 20 5 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0519Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_5_19_0 : RowCompute.yRowIntegralFast 20 5 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_19_1 : RowCompute.yRowIntegralFast 20 5 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_19_2 : RowCompute.yRowIntegralFast 20 5 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_19_3 : RowCompute.yRowIntegralFast 20 5 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_19_4 : RowCompute.yRowIntegralFast 20 5 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_19_5 : RowCompute.yRowIntegralFast 20 5 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_5_19_6 : RowCompute.yRowIntegralFast 20 5 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0707Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_7_7_0 : RowCompute.yRowIntegralFast 20 7 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_7_1 : RowCompute.yRowIntegralFast 20 7 7 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_7_2 : RowCompute.yRowIntegralFast 20 7 7 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_7_3 : RowCompute.yRowIntegralFast 20 7 7 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_7_4 : RowCompute.yRowIntegralFast 20 7 7 (RowCompute.rows[4]!) =
    (265962877776069958562385384930539536332908532617019654144000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_7_5 : RowCompute.yRowIntegralFast 20 7 7 (RowCompute.rows[5]!) =
    (1401568466276564513004011482908906430326956131599519842304000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_7_6 : RowCompute.yRowIntegralFast 20 7 7 (RowCompute.rows[6]!) =
    (249494808189122981969682564394212004904748731349520613376000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0709Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_7_9_0 : RowCompute.yRowIntegralFast 20 7 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_9_1 : RowCompute.yRowIntegralFast 20 7 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_9_2 : RowCompute.yRowIntegralFast 20 7 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_9_3 : RowCompute.yRowIntegralFast 20 7 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_9_4 : RowCompute.yRowIntegralFast 20 7 9 (RowCompute.rows[4]!) =
    (-683045380437834427463028201404441675413410402079082545152000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_9_5 : RowCompute.yRowIntegralFast 20 7 9 (RowCompute.rows[5]!) =
    (-134571392895373863729333053380562395022598733130027237376000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_9_6 : RowCompute.yRowIntegralFast 20 7 9 (RowCompute.rows[6]!) =
    (-115151449933441376293699645105020925340653260622855667712000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0717Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_7_17_0 : RowCompute.yRowIntegralFast 20 7 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_17_1 : RowCompute.yRowIntegralFast 20 7 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_17_2 : RowCompute.yRowIntegralFast 20 7 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_17_3 : RowCompute.yRowIntegralFast 20 7 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_17_4 : RowCompute.yRowIntegralFast 20 7 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_17_5 : RowCompute.yRowIntegralFast 20 7 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_17_6 : RowCompute.yRowIntegralFast 20 7 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0719Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_7_19_0 : RowCompute.yRowIntegralFast 20 7 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_19_1 : RowCompute.yRowIntegralFast 20 7 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_19_2 : RowCompute.yRowIntegralFast 20 7 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_19_3 : RowCompute.yRowIntegralFast 20 7 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_19_4 : RowCompute.yRowIntegralFast 20 7 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_19_5 : RowCompute.yRowIntegralFast 20 7 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_7_19_6 : RowCompute.yRowIntegralFast 20 7 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0909Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_9_9_0 : RowCompute.yRowIntegralFast 20 9 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_9_1 : RowCompute.yRowIntegralFast 20 9 9 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_9_2 : RowCompute.yRowIntegralFast 20 9 9 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_9_3 : RowCompute.yRowIntegralFast 20 9 9 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_9_4 : RowCompute.yRowIntegralFast 20 9 9 (RowCompute.rows[4]!) =
    (1754195907484062975929416169449113023674487123298238857216000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_9_5 : RowCompute.yRowIntegralFast 20 9 9 (RowCompute.rows[5]!) =
    (12920852759987559434346733696151526000673626598926188544000000000 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_9_6 : RowCompute.yRowIntegralFast 20 9 9 (RowCompute.rows[6]!) =
    (-1313736165695597713264874208136315618479490953889129168896000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0917Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_9_17_0 : RowCompute.yRowIntegralFast 20 9 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_17_1 : RowCompute.yRowIntegralFast 20 9 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_17_2 : RowCompute.yRowIntegralFast 20 9 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_17_3 : RowCompute.yRowIntegralFast 20 9 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_17_4 : RowCompute.yRowIntegralFast 20 9 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_17_5 : RowCompute.yRowIntegralFast 20 9 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_17_6 : RowCompute.yRowIntegralFast 20 9 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0919Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_9_19_0 : RowCompute.yRowIntegralFast 20 9 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_19_1 : RowCompute.yRowIntegralFast 20 9 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_19_2 : RowCompute.yRowIntegralFast 20 9 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_19_3 : RowCompute.yRowIntegralFast 20 9 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_19_4 : RowCompute.yRowIntegralFast 20 9 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_19_5 : RowCompute.yRowIntegralFast 20 9 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_9_19_6 : RowCompute.yRowIntegralFast 20 9 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1117Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_11_17_0 : RowCompute.yRowIntegralFast 20 11 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_17_1 : RowCompute.yRowIntegralFast 20 11 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_17_2 : RowCompute.yRowIntegralFast 20 11 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_17_3 : RowCompute.yRowIntegralFast 20 11 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_17_4 : RowCompute.yRowIntegralFast 20 11 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_17_5 : RowCompute.yRowIntegralFast 20 11 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_17_6 : RowCompute.yRowIntegralFast 20 11 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1119Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_11_19_0 : RowCompute.yRowIntegralFast 20 11 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_19_1 : RowCompute.yRowIntegralFast 20 11 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_19_2 : RowCompute.yRowIntegralFast 20 11 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_19_3 : RowCompute.yRowIntegralFast 20 11 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_19_4 : RowCompute.yRowIntegralFast 20 11 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_19_5 : RowCompute.yRowIntegralFast 20 11 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_11_19_6 : RowCompute.yRowIntegralFast 20 11 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1317Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_13_17_0 : RowCompute.yRowIntegralFast 20 13 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_17_1 : RowCompute.yRowIntegralFast 20 13 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_17_2 : RowCompute.yRowIntegralFast 20 13 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_17_3 : RowCompute.yRowIntegralFast 20 13 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_17_4 : RowCompute.yRowIntegralFast 20 13 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_17_5 : RowCompute.yRowIntegralFast 20 13 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_17_6 : RowCompute.yRowIntegralFast 20 13 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1319Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_13_19_0 : RowCompute.yRowIntegralFast 20 13 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_19_1 : RowCompute.yRowIntegralFast 20 13 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_19_2 : RowCompute.yRowIntegralFast 20 13 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_19_3 : RowCompute.yRowIntegralFast 20 13 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_19_4 : RowCompute.yRowIntegralFast 20 13 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_19_5 : RowCompute.yRowIntegralFast 20 13 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_13_19_6 : RowCompute.yRowIntegralFast 20 13 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1517Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_15_17_0 : RowCompute.yRowIntegralFast 20 15 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_17_1 : RowCompute.yRowIntegralFast 20 15 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_17_2 : RowCompute.yRowIntegralFast 20 15 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_17_3 : RowCompute.yRowIntegralFast 20 15 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_17_4 : RowCompute.yRowIntegralFast 20 15 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_17_5 : RowCompute.yRowIntegralFast 20 15 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_17_6 : RowCompute.yRowIntegralFast 20 15 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1519Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_15_19_0 : RowCompute.yRowIntegralFast 20 15 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_19_1 : RowCompute.yRowIntegralFast 20 15 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_19_2 : RowCompute.yRowIntegralFast 20 15 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_19_3 : RowCompute.yRowIntegralFast 20 15 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_19_4 : RowCompute.yRowIntegralFast 20 15 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_19_5 : RowCompute.yRowIntegralFast 20 15 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_15_19_6 : RowCompute.yRowIntegralFast 20 15 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1717Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_17_17_0 : RowCompute.yRowIntegralFast 20 17 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_17_1 : RowCompute.yRowIntegralFast 20 17 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_17_2 : RowCompute.yRowIntegralFast 20 17 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_17_3 : RowCompute.yRowIntegralFast 20 17 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_17_4 : RowCompute.yRowIntegralFast 20 17 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_17_5 : RowCompute.yRowIntegralFast 20 17 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_17_6 : RowCompute.yRowIntegralFast 20 17 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1719Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_17_19_0 : RowCompute.yRowIntegralFast 20 17 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_19_1 : RowCompute.yRowIntegralFast 20 17 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_19_2 : RowCompute.yRowIntegralFast 20 17 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_19_3 : RowCompute.yRowIntegralFast 20 17 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_19_4 : RowCompute.yRowIntegralFast 20 17 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_19_5 : RowCompute.yRowIntegralFast 20 17 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_17_19_6 : RowCompute.yRowIntegralFast 20 17 19 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1919Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_20_19_19_0 : RowCompute.yRowIntegralFast 20 19 19 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_19_19_1 : RowCompute.yRowIntegralFast 20 19 19 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_19_19_2 : RowCompute.yRowIntegralFast 20 19 19 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_19_19_3 : RowCompute.yRowIntegralFast 20 19 19 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_19_19_4 : RowCompute.yRowIntegralFast 20 19 19 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_19_19_5 : RowCompute.yRowIntegralFast 20 19 19 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_20_19_19_6 : RowCompute.yRowIntegralFast 20 19 19 (RowCompute.rows[6]!) =
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_20_1_7 : Y 20 1 7 = (665376664948039201360203/40960000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 1 7 0 (by decide),
    source_yRow_eq_rowCompute 20 1 7 1 (by decide),
    source_yRow_eq_rowCompute 20 1 7 2 (by decide),
    source_yRow_eq_rowCompute 20 1 7 3 (by decide),
    source_yRow_eq_rowCompute 20 1 7 4 (by decide),
    source_yRow_eq_rowCompute 20 1 7 5 (by decide),
    source_yRow_eq_rowCompute 20 1 7 6 (by decide),
    computeRow_20_1_7_0, computeRow_20_1_7_1, computeRow_20_1_7_2, computeRow_20_1_7_3, computeRow_20_1_7_4, computeRow_20_1_7_5, computeRow_20_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_1_17 : Y 20 1 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 1 17 0 (by decide),
    source_yRow_eq_rowCompute 20 1 17 1 (by decide),
    source_yRow_eq_rowCompute 20 1 17 2 (by decide),
    source_yRow_eq_rowCompute 20 1 17 3 (by decide),
    source_yRow_eq_rowCompute 20 1 17 4 (by decide),
    source_yRow_eq_rowCompute 20 1 17 5 (by decide),
    source_yRow_eq_rowCompute 20 1 17 6 (by decide),
    computeRow_20_1_17_0, computeRow_20_1_17_1, computeRow_20_1_17_2, computeRow_20_1_17_3, computeRow_20_1_17_4, computeRow_20_1_17_5, computeRow_20_1_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_1_19 : Y 20 1 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 1 19 0 (by decide),
    source_yRow_eq_rowCompute 20 1 19 1 (by decide),
    source_yRow_eq_rowCompute 20 1 19 2 (by decide),
    source_yRow_eq_rowCompute 20 1 19 3 (by decide),
    source_yRow_eq_rowCompute 20 1 19 4 (by decide),
    source_yRow_eq_rowCompute 20 1 19 5 (by decide),
    source_yRow_eq_rowCompute 20 1 19 6 (by decide),
    computeRow_20_1_19_0, computeRow_20_1_19_1, computeRow_20_1_19_2, computeRow_20_1_19_3, computeRow_20_1_19_4, computeRow_20_1_19_5, computeRow_20_1_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_3_9 : Y 20 3 9 = (30613754919741298283979/10240000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 3 9 0 (by decide),
    source_yRow_eq_rowCompute 20 3 9 1 (by decide),
    source_yRow_eq_rowCompute 20 3 9 2 (by decide),
    source_yRow_eq_rowCompute 20 3 9 3 (by decide),
    source_yRow_eq_rowCompute 20 3 9 4 (by decide),
    source_yRow_eq_rowCompute 20 3 9 5 (by decide),
    source_yRow_eq_rowCompute 20 3 9 6 (by decide),
    computeRow_20_3_9_0, computeRow_20_3_9_1, computeRow_20_3_9_2, computeRow_20_3_9_3, computeRow_20_3_9_4, computeRow_20_3_9_5, computeRow_20_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_3_17 : Y 20 3 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 3 17 0 (by decide),
    source_yRow_eq_rowCompute 20 3 17 1 (by decide),
    source_yRow_eq_rowCompute 20 3 17 2 (by decide),
    source_yRow_eq_rowCompute 20 3 17 3 (by decide),
    source_yRow_eq_rowCompute 20 3 17 4 (by decide),
    source_yRow_eq_rowCompute 20 3 17 5 (by decide),
    source_yRow_eq_rowCompute 20 3 17 6 (by decide),
    computeRow_20_3_17_0, computeRow_20_3_17_1, computeRow_20_3_17_2, computeRow_20_3_17_3, computeRow_20_3_17_4, computeRow_20_3_17_5, computeRow_20_3_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_3_19 : Y 20 3 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 3 19 0 (by decide),
    source_yRow_eq_rowCompute 20 3 19 1 (by decide),
    source_yRow_eq_rowCompute 20 3 19 2 (by decide),
    source_yRow_eq_rowCompute 20 3 19 3 (by decide),
    source_yRow_eq_rowCompute 20 3 19 4 (by decide),
    source_yRow_eq_rowCompute 20 3 19 5 (by decide),
    source_yRow_eq_rowCompute 20 3 19 6 (by decide),
    computeRow_20_3_19_0, computeRow_20_3_19_1, computeRow_20_3_19_2, computeRow_20_3_19_3, computeRow_20_3_19_4, computeRow_20_3_19_5, computeRow_20_3_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_5_7 : Y 20 5 7 = (97684912586085571093347/32768000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 5 7 0 (by decide),
    source_yRow_eq_rowCompute 20 5 7 1 (by decide),
    source_yRow_eq_rowCompute 20 5 7 2 (by decide),
    source_yRow_eq_rowCompute 20 5 7 3 (by decide),
    source_yRow_eq_rowCompute 20 5 7 4 (by decide),
    source_yRow_eq_rowCompute 20 5 7 5 (by decide),
    source_yRow_eq_rowCompute 20 5 7 6 (by decide),
    computeRow_20_5_7_0, computeRow_20_5_7_1, computeRow_20_5_7_2, computeRow_20_5_7_3, computeRow_20_5_7_4, computeRow_20_5_7_5, computeRow_20_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_5_9 : Y 20 5 9 = (-11858364672253510424013/8192000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 5 9 0 (by decide),
    source_yRow_eq_rowCompute 20 5 9 1 (by decide),
    source_yRow_eq_rowCompute 20 5 9 2 (by decide),
    source_yRow_eq_rowCompute 20 5 9 3 (by decide),
    source_yRow_eq_rowCompute 20 5 9 4 (by decide),
    source_yRow_eq_rowCompute 20 5 9 5 (by decide),
    source_yRow_eq_rowCompute 20 5 9 6 (by decide),
    computeRow_20_5_9_0, computeRow_20_5_9_1, computeRow_20_5_9_2, computeRow_20_5_9_3, computeRow_20_5_9_4, computeRow_20_5_9_5, computeRow_20_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_5_17 : Y 20 5 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 5 17 0 (by decide),
    source_yRow_eq_rowCompute 20 5 17 1 (by decide),
    source_yRow_eq_rowCompute 20 5 17 2 (by decide),
    source_yRow_eq_rowCompute 20 5 17 3 (by decide),
    source_yRow_eq_rowCompute 20 5 17 4 (by decide),
    source_yRow_eq_rowCompute 20 5 17 5 (by decide),
    source_yRow_eq_rowCompute 20 5 17 6 (by decide),
    computeRow_20_5_17_0, computeRow_20_5_17_1, computeRow_20_5_17_2, computeRow_20_5_17_3, computeRow_20_5_17_4, computeRow_20_5_17_5, computeRow_20_5_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_5_19 : Y 20 5 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 5 19 0 (by decide),
    source_yRow_eq_rowCompute 20 5 19 1 (by decide),
    source_yRow_eq_rowCompute 20 5 19 2 (by decide),
    source_yRow_eq_rowCompute 20 5 19 3 (by decide),
    source_yRow_eq_rowCompute 20 5 19 4 (by decide),
    source_yRow_eq_rowCompute 20 5 19 5 (by decide),
    source_yRow_eq_rowCompute 20 5 19 6 (by decide),
    computeRow_20_5_19_0, computeRow_20_5_19_1, computeRow_20_5_19_2, computeRow_20_5_19_3, computeRow_20_5_19_4, computeRow_20_5_19_5, computeRow_20_5_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_7_7 : Y 20 7 7 = (-54884862420967333061307/32768000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 7 7 0 (by decide),
    source_yRow_eq_rowCompute 20 7 7 1 (by decide),
    source_yRow_eq_rowCompute 20 7 7 2 (by decide),
    source_yRow_eq_rowCompute 20 7 7 3 (by decide),
    source_yRow_eq_rowCompute 20 7 7 4 (by decide),
    source_yRow_eq_rowCompute 20 7 7 5 (by decide),
    source_yRow_eq_rowCompute 20 7 7 6 (by decide),
    computeRow_20_7_7_0, computeRow_20_7_7_1, computeRow_20_7_7_2, computeRow_20_7_7_3, computeRow_20_7_7_4, computeRow_20_7_7_5, computeRow_20_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_7_9 : Y 20 7 9 = (333816883149802681629/409600000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 7 9 0 (by decide),
    source_yRow_eq_rowCompute 20 7 9 1 (by decide),
    source_yRow_eq_rowCompute 20 7 9 2 (by decide),
    source_yRow_eq_rowCompute 20 7 9 3 (by decide),
    source_yRow_eq_rowCompute 20 7 9 4 (by decide),
    source_yRow_eq_rowCompute 20 7 9 5 (by decide),
    source_yRow_eq_rowCompute 20 7 9 6 (by decide),
    computeRow_20_7_9_0, computeRow_20_7_9_1, computeRow_20_7_9_2, computeRow_20_7_9_3, computeRow_20_7_9_4, computeRow_20_7_9_5, computeRow_20_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_7_17 : Y 20 7 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 7 17 0 (by decide),
    source_yRow_eq_rowCompute 20 7 17 1 (by decide),
    source_yRow_eq_rowCompute 20 7 17 2 (by decide),
    source_yRow_eq_rowCompute 20 7 17 3 (by decide),
    source_yRow_eq_rowCompute 20 7 17 4 (by decide),
    source_yRow_eq_rowCompute 20 7 17 5 (by decide),
    source_yRow_eq_rowCompute 20 7 17 6 (by decide),
    computeRow_20_7_17_0, computeRow_20_7_17_1, computeRow_20_7_17_2, computeRow_20_7_17_3, computeRow_20_7_17_4, computeRow_20_7_17_5, computeRow_20_7_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_7_19 : Y 20 7 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 7 19 0 (by decide),
    source_yRow_eq_rowCompute 20 7 19 1 (by decide),
    source_yRow_eq_rowCompute 20 7 19 2 (by decide),
    source_yRow_eq_rowCompute 20 7 19 3 (by decide),
    source_yRow_eq_rowCompute 20 7 19 4 (by decide),
    source_yRow_eq_rowCompute 20 7 19 5 (by decide),
    source_yRow_eq_rowCompute 20 7 19 6 (by decide),
    computeRow_20_7_19_0, computeRow_20_7_19_1, computeRow_20_7_19_2, computeRow_20_7_19_3, computeRow_20_7_19_4, computeRow_20_7_19_5, computeRow_20_7_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_9_9 : Y 20 9 9 = (-405636934175189416161/1024000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 9 9 0 (by decide),
    source_yRow_eq_rowCompute 20 9 9 1 (by decide),
    source_yRow_eq_rowCompute 20 9 9 2 (by decide),
    source_yRow_eq_rowCompute 20 9 9 3 (by decide),
    source_yRow_eq_rowCompute 20 9 9 4 (by decide),
    source_yRow_eq_rowCompute 20 9 9 5 (by decide),
    source_yRow_eq_rowCompute 20 9 9 6 (by decide),
    computeRow_20_9_9_0, computeRow_20_9_9_1, computeRow_20_9_9_2, computeRow_20_9_9_3, computeRow_20_9_9_4, computeRow_20_9_9_5, computeRow_20_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_9_17 : Y 20 9 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 9 17 0 (by decide),
    source_yRow_eq_rowCompute 20 9 17 1 (by decide),
    source_yRow_eq_rowCompute 20 9 17 2 (by decide),
    source_yRow_eq_rowCompute 20 9 17 3 (by decide),
    source_yRow_eq_rowCompute 20 9 17 4 (by decide),
    source_yRow_eq_rowCompute 20 9 17 5 (by decide),
    source_yRow_eq_rowCompute 20 9 17 6 (by decide),
    computeRow_20_9_17_0, computeRow_20_9_17_1, computeRow_20_9_17_2, computeRow_20_9_17_3, computeRow_20_9_17_4, computeRow_20_9_17_5, computeRow_20_9_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_9_19 : Y 20 9 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 9 19 0 (by decide),
    source_yRow_eq_rowCompute 20 9 19 1 (by decide),
    source_yRow_eq_rowCompute 20 9 19 2 (by decide),
    source_yRow_eq_rowCompute 20 9 19 3 (by decide),
    source_yRow_eq_rowCompute 20 9 19 4 (by decide),
    source_yRow_eq_rowCompute 20 9 19 5 (by decide),
    source_yRow_eq_rowCompute 20 9 19 6 (by decide),
    computeRow_20_9_19_0, computeRow_20_9_19_1, computeRow_20_9_19_2, computeRow_20_9_19_3, computeRow_20_9_19_4, computeRow_20_9_19_5, computeRow_20_9_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_11_17 : Y 20 11 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 11 17 0 (by decide),
    source_yRow_eq_rowCompute 20 11 17 1 (by decide),
    source_yRow_eq_rowCompute 20 11 17 2 (by decide),
    source_yRow_eq_rowCompute 20 11 17 3 (by decide),
    source_yRow_eq_rowCompute 20 11 17 4 (by decide),
    source_yRow_eq_rowCompute 20 11 17 5 (by decide),
    source_yRow_eq_rowCompute 20 11 17 6 (by decide),
    computeRow_20_11_17_0, computeRow_20_11_17_1, computeRow_20_11_17_2, computeRow_20_11_17_3, computeRow_20_11_17_4, computeRow_20_11_17_5, computeRow_20_11_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_11_19 : Y 20 11 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 11 19 0 (by decide),
    source_yRow_eq_rowCompute 20 11 19 1 (by decide),
    source_yRow_eq_rowCompute 20 11 19 2 (by decide),
    source_yRow_eq_rowCompute 20 11 19 3 (by decide),
    source_yRow_eq_rowCompute 20 11 19 4 (by decide),
    source_yRow_eq_rowCompute 20 11 19 5 (by decide),
    source_yRow_eq_rowCompute 20 11 19 6 (by decide),
    computeRow_20_11_19_0, computeRow_20_11_19_1, computeRow_20_11_19_2, computeRow_20_11_19_3, computeRow_20_11_19_4, computeRow_20_11_19_5, computeRow_20_11_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_13_17 : Y 20 13 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 13 17 0 (by decide),
    source_yRow_eq_rowCompute 20 13 17 1 (by decide),
    source_yRow_eq_rowCompute 20 13 17 2 (by decide),
    source_yRow_eq_rowCompute 20 13 17 3 (by decide),
    source_yRow_eq_rowCompute 20 13 17 4 (by decide),
    source_yRow_eq_rowCompute 20 13 17 5 (by decide),
    source_yRow_eq_rowCompute 20 13 17 6 (by decide),
    computeRow_20_13_17_0, computeRow_20_13_17_1, computeRow_20_13_17_2, computeRow_20_13_17_3, computeRow_20_13_17_4, computeRow_20_13_17_5, computeRow_20_13_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_13_19 : Y 20 13 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 13 19 0 (by decide),
    source_yRow_eq_rowCompute 20 13 19 1 (by decide),
    source_yRow_eq_rowCompute 20 13 19 2 (by decide),
    source_yRow_eq_rowCompute 20 13 19 3 (by decide),
    source_yRow_eq_rowCompute 20 13 19 4 (by decide),
    source_yRow_eq_rowCompute 20 13 19 5 (by decide),
    source_yRow_eq_rowCompute 20 13 19 6 (by decide),
    computeRow_20_13_19_0, computeRow_20_13_19_1, computeRow_20_13_19_2, computeRow_20_13_19_3, computeRow_20_13_19_4, computeRow_20_13_19_5, computeRow_20_13_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_15_17 : Y 20 15 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 15 17 0 (by decide),
    source_yRow_eq_rowCompute 20 15 17 1 (by decide),
    source_yRow_eq_rowCompute 20 15 17 2 (by decide),
    source_yRow_eq_rowCompute 20 15 17 3 (by decide),
    source_yRow_eq_rowCompute 20 15 17 4 (by decide),
    source_yRow_eq_rowCompute 20 15 17 5 (by decide),
    source_yRow_eq_rowCompute 20 15 17 6 (by decide),
    computeRow_20_15_17_0, computeRow_20_15_17_1, computeRow_20_15_17_2, computeRow_20_15_17_3, computeRow_20_15_17_4, computeRow_20_15_17_5, computeRow_20_15_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_15_19 : Y 20 15 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 15 19 0 (by decide),
    source_yRow_eq_rowCompute 20 15 19 1 (by decide),
    source_yRow_eq_rowCompute 20 15 19 2 (by decide),
    source_yRow_eq_rowCompute 20 15 19 3 (by decide),
    source_yRow_eq_rowCompute 20 15 19 4 (by decide),
    source_yRow_eq_rowCompute 20 15 19 5 (by decide),
    source_yRow_eq_rowCompute 20 15 19 6 (by decide),
    computeRow_20_15_19_0, computeRow_20_15_19_1, computeRow_20_15_19_2, computeRow_20_15_19_3, computeRow_20_15_19_4, computeRow_20_15_19_5, computeRow_20_15_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_17_17 : Y 20 17 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 17 17 0 (by decide),
    source_yRow_eq_rowCompute 20 17 17 1 (by decide),
    source_yRow_eq_rowCompute 20 17 17 2 (by decide),
    source_yRow_eq_rowCompute 20 17 17 3 (by decide),
    source_yRow_eq_rowCompute 20 17 17 4 (by decide),
    source_yRow_eq_rowCompute 20 17 17 5 (by decide),
    source_yRow_eq_rowCompute 20 17 17 6 (by decide),
    computeRow_20_17_17_0, computeRow_20_17_17_1, computeRow_20_17_17_2, computeRow_20_17_17_3, computeRow_20_17_17_4, computeRow_20_17_17_5, computeRow_20_17_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_17_19 : Y 20 17 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 17 19 0 (by decide),
    source_yRow_eq_rowCompute 20 17 19 1 (by decide),
    source_yRow_eq_rowCompute 20 17 19 2 (by decide),
    source_yRow_eq_rowCompute 20 17 19 3 (by decide),
    source_yRow_eq_rowCompute 20 17 19 4 (by decide),
    source_yRow_eq_rowCompute 20 17 19 5 (by decide),
    source_yRow_eq_rowCompute 20 17 19 6 (by decide),
    computeRow_20_17_19_0, computeRow_20_17_19_1, computeRow_20_17_19_2, computeRow_20_17_19_3, computeRow_20_17_19_4, computeRow_20_17_19_5, computeRow_20_17_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_20_19_19 : Y 20 19 19 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 20 19 19 0 (by decide),
    source_yRow_eq_rowCompute 20 19 19 1 (by decide),
    source_yRow_eq_rowCompute 20 19 19 2 (by decide),
    source_yRow_eq_rowCompute 20 19 19 3 (by decide),
    source_yRow_eq_rowCompute 20 19 19 4 (by decide),
    source_yRow_eq_rowCompute 20 19 19 5 (by decide),
    source_yRow_eq_rowCompute 20 19 19 6 (by decide),
    computeRow_20_19_19_0, computeRow_20_19_19_1, computeRow_20_19_19_2, computeRow_20_19_19_3, computeRow_20_19_19_4, computeRow_20_19_19_5, computeRow_20_19_19_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem error_20_oai : errorRational 20 = candidateY_20 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_20_1_1
  · exact source_error_20_1_3
  · exact source_error_20_1_5
  · exact source_error_20_1_7
  · exact source_error_20_1_9
  · exact source_error_20_1_11
  · exact source_error_20_1_13
  · exact source_error_20_1_15
  · exact source_error_20_1_17
  · exact source_error_20_1_19
  · exact source_error_20_3_1
  · exact source_error_20_3_3
  · exact source_error_20_3_5
  · exact source_error_20_3_7
  · exact source_error_20_3_9
  · exact source_error_20_3_11
  · exact source_error_20_3_13
  · exact source_error_20_3_15
  · exact source_error_20_3_17
  · exact source_error_20_3_19
  · exact source_error_20_5_1
  · exact source_error_20_5_3
  · exact source_error_20_5_5
  · exact source_error_20_5_7
  · exact source_error_20_5_9
  · exact source_error_20_5_11
  · exact source_error_20_5_13
  · exact source_error_20_5_15
  · exact source_error_20_5_17
  · exact source_error_20_5_19
  · exact source_error_20_7_1
  · exact source_error_20_7_3
  · exact source_error_20_7_5
  · exact source_error_20_7_7
  · exact source_error_20_7_9
  · exact source_error_20_7_11
  · exact source_error_20_7_13
  · exact source_error_20_7_15
  · exact source_error_20_7_17
  · exact source_error_20_7_19
  · exact source_error_20_9_1
  · exact source_error_20_9_3
  · exact source_error_20_9_5
  · exact source_error_20_9_7
  · exact source_error_20_9_9
  · exact source_error_20_9_11
  · exact source_error_20_9_13
  · exact source_error_20_9_15
  · exact source_error_20_9_17
  · exact source_error_20_9_19
  · exact source_error_20_11_1
  · exact source_error_20_11_3
  · exact source_error_20_11_5
  · exact source_error_20_11_7
  · exact source_error_20_11_9
  · exact source_error_20_11_11
  · exact source_error_20_11_13
  · exact source_error_20_11_15
  · exact source_error_20_11_17
  · exact source_error_20_11_19
  · exact source_error_20_13_1
  · exact source_error_20_13_3
  · exact source_error_20_13_5
  · exact source_error_20_13_7
  · exact source_error_20_13_9
  · exact source_error_20_13_11
  · exact source_error_20_13_13
  · exact source_error_20_13_15
  · exact source_error_20_13_17
  · exact source_error_20_13_19
  · exact source_error_20_15_1
  · exact source_error_20_15_3
  · exact source_error_20_15_5
  · exact source_error_20_15_7
  · exact source_error_20_15_9
  · exact source_error_20_15_11
  · exact source_error_20_15_13
  · exact source_error_20_15_15
  · exact source_error_20_15_17
  · exact source_error_20_15_19
  · exact source_error_20_17_1
  · exact source_error_20_17_3
  · exact source_error_20_17_5
  · exact source_error_20_17_7
  · exact source_error_20_17_9
  · exact source_error_20_17_11
  · exact source_error_20_17_13
  · exact source_error_20_17_15
  · exact source_error_20_17_17
  · exact source_error_20_17_19
  · exact source_error_20_19_1
  · exact source_error_20_19_3
  · exact source_error_20_19_5
  · exact source_error_20_19_7
  · exact source_error_20_19_9
  · exact source_error_20_19_11
  · exact source_error_20_19_13
  · exact source_error_20_19_15
  · exact source_error_20_19_17
  · exact source_error_20_19_19

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_20_oai := @OAI.Laughlin.Certificate.error_20_oai
