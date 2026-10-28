-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:29:45.805985+00:00
-- url     : https://prove2.me/submissions/b175d84c-5527-4b64-be4e-4a7ae438eeb0

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_23

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_23 : GramCompute.quadruples 23 = [(0,1,2,21), (0,1,3,20), (0,1,4,19), (0,1,5,18), (0,1,6,17), (0,1,7,16), (0,1,8,15), (0,1,9,14), (0,1,10,13), (0,1,11,12), (0,2,3,19), (0,2,4,18), (0,2,5,17), (0,2,6,16), (0,2,7,15), (0,2,8,14), (0,2,9,13), (0,2,10,12), (0,3,4,17), (0,3,5,16), (0,3,6,15), (0,3,7,14), (0,3,8,13), (0,3,9,12), (0,3,10,11), (0,4,5,15), (0,4,6,14), (0,4,7,13), (0,4,8,12), (0,4,9,11), (0,5,6,13), (0,5,7,12), (0,5,8,11), (0,5,9,10), (0,6,7,11), (0,6,8,10), (0,7,8,9), (1,2,3,18), (1,2,4,17), (1,2,5,16), (1,2,6,15), (1,2,7,14), (1,2,8,13), (1,2,9,12), (1,2,10,11), (1,3,4,16), (1,3,5,15), (1,3,6,14), (1,3,7,13), (1,3,8,12), (1,3,9,11), (1,4,5,14), (1,4,6,13), (1,4,7,12), (1,4,8,11), (1,4,9,10), (1,5,6,12), (1,5,7,11), (1,5,8,10), (1,6,7,10), (1,6,8,9), (2,3,4,15), (2,3,5,14), (2,3,6,13), (2,3,7,12), (2,3,8,11), (2,3,9,10), (2,4,5,13), (2,4,6,12), (2,4,7,11), (2,4,8,10), (2,5,6,11), (2,5,7,10), (2,5,8,9), (2,6,7,9), (3,4,5,12), (3,4,6,11), (3,4,7,10), (3,4,8,9), (3,5,6,10), (3,5,7,9), (3,6,7,8), (4,5,6,9), (4,5,7,8)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram01Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_1_1 : GramCompute.ZFast 23 1 1 = (2248001455555215360000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_3 : GramCompute.ZFast 23 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_5 : GramCompute.ZFast 23 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_7 : GramCompute.ZFast 23 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_9 : GramCompute.ZFast 23 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_11 : GramCompute.ZFast 23 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_13 : GramCompute.ZFast 23 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_15 : GramCompute.ZFast 23 1 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_17 : GramCompute.ZFast 23 1 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_19 : GramCompute.ZFast 23 1 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_21 : GramCompute.ZFast 23 1 21 = (-2195313921440640000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_1_23 : GramCompute.ZFast 23 1 23 = (252461100965673600000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram03Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_3_3 : GramCompute.ZFast 23 3 3 = (14597412049059840000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_5 : GramCompute.ZFast 23 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_7 : GramCompute.ZFast 23 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_9 : GramCompute.ZFast 23 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_11 : GramCompute.ZFast 23 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_13 : GramCompute.ZFast 23 3 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_15 : GramCompute.ZFast 23 3 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_17 : GramCompute.ZFast 23 3 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_19 : GramCompute.ZFast 23 3 19 = (-57021140816640000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_21 : GramCompute.ZFast 23 3 21 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_3_23 : GramCompute.ZFast 23 3 23 = (100984440386269440000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram05Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_5_5 : GramCompute.ZFast 23 5 5 = (768284844687360000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_7 : GramCompute.ZFast 23 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_9 : GramCompute.ZFast 23 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_11 : GramCompute.ZFast 23 5 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_13 : GramCompute.ZFast 23 5 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_15 : GramCompute.ZFast 23 5 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_17 : GramCompute.ZFast 23 5 17 = (-4501669011840000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_19 : GramCompute.ZFast 23 5 19 = (-114042281633280000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_21 : GramCompute.ZFast 23 5 21 = (1746272437509600000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_5_23 : GramCompute.ZFast 23 5 23 = (37869165144851040000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram07Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_7_7 : GramCompute.ZFast 23 7 7 = (105450861035520000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_7_9 : GramCompute.ZFast 23 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_7_11 : GramCompute.ZFast 23 7 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_7_13 : GramCompute.ZFast 23 7 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_7_15 : GramCompute.ZFast 23 7 15 = (-823834851840000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_7_17 : GramCompute.ZFast 23 7 17 = (-24509086842240000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_7_19 : GramCompute.ZFast 23 7 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_7_21 : GramCompute.ZFast 23 7 21 = (1746272437509600000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_7_23 : GramCompute.ZFast 23 7 23 = (12623055048283680000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_9_9 : GramCompute.ZFast 23 9 9 = (31635258310656000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_9_11 : GramCompute.ZFast 23 9 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_9_13 : GramCompute.ZFast 23 9 13 = (-308938069440000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_9_15 : GramCompute.ZFast 23 9 15 = (-8341327874880000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_9_17 : GramCompute.ZFast 23 9 17 = (-26259735902400000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_9_19 : GramCompute.ZFast 23 9 19 = (119744395714944000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_9_21 : GramCompute.ZFast 23 9 21 = (1010343338844840000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_9_23 : GramCompute.ZFast 23 9 23 = (3155763762070920000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram11Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_11_11 : GramCompute.ZFast 23 11 11 = (18896146093440000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_11_13 : GramCompute.ZFast 23 11 13 = (-4854741091200000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_11_15 : GramCompute.ZFast 23 11 15 = (-16991593819200000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_11_17 : GramCompute.ZFast 23 11 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_11_19 : GramCompute.ZFast 23 11 19 = (117606102934320000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_11_21 : GramCompute.ZFast 23 11 21 = (274414240180080000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_11_23 : GramCompute.ZFast 23 11 23 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram13Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_13_13 : GramCompute.ZFast 23 13 13 = (8396495387280000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_13_15 : GramCompute.ZFast 23 13 15 = (-11044535982480000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_13_17 : GramCompute.ZFast 23 13 17 = (13411222264440000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_13_19 : GramCompute.ZFast 23 13 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_13_21 : GramCompute.ZFast 23 13 21 = (-202692336496650000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_13_23 : GramCompute.ZFast 23 13 23 = (-788940940517730000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram15Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_15_15 : GramCompute.ZFast 23 15 15 = (52725430517760000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_15_17 : GramCompute.ZFast 23 15 17 = (-31292851950360000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_15_19 : GramCompute.ZFast 23 15 19 = (-162153869197320000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_15_21 : GramCompute.ZFast 23 15 21 = (-420976391185350000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_15_23 : GramCompute.ZFast 23 15 23 = (-788940940517730000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram17Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_17_17 : GramCompute.ZFast 23 17 17 = (111009907368360000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_17_19 : GramCompute.ZFast 23 17 19 = (-302924810588400000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_17_21 : GramCompute.ZFast 23 17 21 = (-463853616213487500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_17_23 : GramCompute.ZFast 23 17 23 = (-591705705388297500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram19Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_19_19 : GramCompute.ZFast 23 19 19 = (2530981340232345000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_19_21 : GramCompute.ZFast 23 19 21 = (-414739703908530000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_19_23 : GramCompute.ZFast 23 19 23 = (-394470470258865000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram21Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_21_21 : GramCompute.ZFast 23 21 21 = (101850365435360416875 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_21_23 : GramCompute.ZFast 23 21 23 = (-246544043911790625 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram232323
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_23_23 : GramCompute.ZFast 23 23 23 = (25851868812458629565625 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_MatrixCompute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate.MatrixCompute

open scoped BigOperators

theorem middle_apply (D : ℕ) (Y : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    middle D Y i j =
      (if i = j then ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D i else 0) -
        copyWeight D i * Y i j * copyWeight D j := by
  simp only [middle, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply]

theorem compressed_apply (D : ℕ) (Y Z : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    compressed D Y Z i j =
      ∑ k, (∑ l, Z i l *
        ((if l = k then ((if copyLabel l = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D l else 0) -
          copyWeight D l * Y l k * copyWeight D k)) * Z k j := by
  simp only [compressed, Matrix.mul_apply, middle_apply]

theorem ldl_apply {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (i j : Fin n) :
    (L * Matrix.diagonal d * L.transpose) i j = ∑ k, L i k * d k * L j k := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

end Laughlin.Certificate.MatrixCompute

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL00Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_0_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL01Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_1_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL02Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_2_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL03Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_3_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_3_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 3 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 3 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL04Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_4_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_4_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 4 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 4 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL05Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_5_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_5_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 5 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 5 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL06Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_6_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_6_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 6 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 6 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL07Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_7_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_7_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 7 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 7 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL08Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_8_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_8_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 8 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 8 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL09Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_9_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_9_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 9 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 9 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL10Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_10_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_10_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 10 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 10 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL11Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_11_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_10 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 10 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_11_11 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 11 11 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 11 11 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

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

theorem L_eq_fast (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : L D r A = LFast D r A := by
  simp only [L, LFast, V_eq_fast]

theorem Z_eq_fast (D r s : ℕ) : Z D r s = ZFast D r s := by
  simp only [Z, ZFast, L_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_NumericBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem Z_eq_gramCompute (D r s : ℕ) : Z D r s = GramCompute.ZFast D r s := by
  exact Z_eq_fast D r s

theorem compressedRational_eq_compute (D : ℕ) :
    compressedRational D = MatrixCompute.compressed D (errorRational D) (gramRational D) := by
  rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem Z_symm (D r s : ℕ) : Z D r s = Z D s r := by
  unfold Z
  congr 1
  apply List.map_congr_left
  intro A hA
  dsimp
  ring

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

theorem source_gram_23_1_1 : Z 23 1 1 = (2248001455555215360000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_1

theorem source_gram_23_1_3 : Z 23 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_3

theorem source_gram_23_1_5 : Z 23 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_5

theorem source_gram_23_1_7 : Z 23 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_7

theorem source_gram_23_1_9 : Z 23 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_9

theorem source_gram_23_1_11 : Z 23 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_11

theorem source_gram_23_1_13 : Z 23 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_13

theorem source_gram_23_1_15 : Z 23 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_15

theorem source_gram_23_1_17 : Z 23 1 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_17

theorem source_gram_23_1_19 : Z 23 1 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_19

theorem source_gram_23_1_21 : Z 23 1 21 = (-2195313921440640000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_21

theorem source_gram_23_1_23 : Z 23 1 23 = (252461100965673600000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_1_23

theorem source_gram_23_3_3 : Z 23 3 3 = (14597412049059840000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_3

theorem source_gram_23_3_5 : Z 23 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_5

theorem source_gram_23_3_7 : Z 23 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_7

theorem source_gram_23_3_9 : Z 23 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_9

theorem source_gram_23_3_11 : Z 23 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_11

theorem source_gram_23_3_13 : Z 23 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_13

theorem source_gram_23_3_15 : Z 23 3 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_15

theorem source_gram_23_3_17 : Z 23 3 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_17

theorem source_gram_23_3_19 : Z 23 3 19 = (-57021140816640000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_19

theorem source_gram_23_3_21 : Z 23 3 21 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_21

theorem source_gram_23_3_23 : Z 23 3 23 = (100984440386269440000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_23

theorem source_gram_23_5_5 : Z 23 5 5 = (768284844687360000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_5

theorem source_gram_23_5_7 : Z 23 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_7

theorem source_gram_23_5_9 : Z 23 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_9

theorem source_gram_23_5_11 : Z 23 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_11

theorem source_gram_23_5_13 : Z 23 5 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_13

theorem source_gram_23_5_15 : Z 23 5 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_15

theorem source_gram_23_5_17 : Z 23 5 17 = (-4501669011840000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_17

theorem source_gram_23_5_19 : Z 23 5 19 = (-114042281633280000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_19

theorem source_gram_23_5_21 : Z 23 5 21 = (1746272437509600000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_21

theorem source_gram_23_5_23 : Z 23 5 23 = (37869165144851040000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_23

theorem source_gram_23_7_7 : Z 23 7 7 = (105450861035520000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_7

theorem source_gram_23_7_9 : Z 23 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_9

theorem source_gram_23_7_11 : Z 23 7 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_11

theorem source_gram_23_7_13 : Z 23 7 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_13

theorem source_gram_23_7_15 : Z 23 7 15 = (-823834851840000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_15

theorem source_gram_23_7_17 : Z 23 7 17 = (-24509086842240000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_17

theorem source_gram_23_7_19 : Z 23 7 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_19

theorem source_gram_23_7_21 : Z 23 7 21 = (1746272437509600000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_21

theorem source_gram_23_7_23 : Z 23 7 23 = (12623055048283680000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_7_23

theorem source_gram_23_9_9 : Z 23 9 9 = (31635258310656000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_9_9

theorem source_gram_23_9_11 : Z 23 9 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_9_11

theorem source_gram_23_9_13 : Z 23 9 13 = (-308938069440000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_9_13

theorem source_gram_23_9_15 : Z 23 9 15 = (-8341327874880000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_9_15

theorem source_gram_23_9_17 : Z 23 9 17 = (-26259735902400000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_9_17

theorem source_gram_23_9_19 : Z 23 9 19 = (119744395714944000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_9_19

theorem source_gram_23_9_21 : Z 23 9 21 = (1010343338844840000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_9_21

theorem source_gram_23_9_23 : Z 23 9 23 = (3155763762070920000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_9_23

theorem source_gram_23_11_11 : Z 23 11 11 = (18896146093440000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_11_11

theorem source_gram_23_11_13 : Z 23 11 13 = (-4854741091200000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_11_13

theorem source_gram_23_11_15 : Z 23 11 15 = (-16991593819200000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_11_15

theorem source_gram_23_11_17 : Z 23 11 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_11_17

theorem source_gram_23_11_19 : Z 23 11 19 = (117606102934320000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_11_19

theorem source_gram_23_11_21 : Z 23 11 21 = (274414240180080000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_11_21

theorem source_gram_23_11_23 : Z 23 11 23 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_11_23

theorem source_gram_23_13_13 : Z 23 13 13 = (8396495387280000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_13_13

theorem source_gram_23_13_15 : Z 23 13 15 = (-11044535982480000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_13_15

theorem source_gram_23_13_17 : Z 23 13 17 = (13411222264440000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_13_17

theorem source_gram_23_13_19 : Z 23 13 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_13_19

theorem source_gram_23_13_21 : Z 23 13 21 = (-202692336496650000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_13_21

theorem source_gram_23_13_23 : Z 23 13 23 = (-788940940517730000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_13_23

theorem source_gram_23_15_15 : Z 23 15 15 = (52725430517760000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_15_15

theorem source_gram_23_15_17 : Z 23 15 17 = (-31292851950360000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_15_17

theorem source_gram_23_15_19 : Z 23 15 19 = (-162153869197320000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_15_19

theorem source_gram_23_15_21 : Z 23 15 21 = (-420976391185350000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_15_21

theorem source_gram_23_15_23 : Z 23 15 23 = (-788940940517730000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_15_23

theorem source_gram_23_17_17 : Z 23 17 17 = (111009907368360000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_17_17

theorem source_gram_23_17_19 : Z 23 17 19 = (-302924810588400000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_17_19

theorem source_gram_23_17_21 : Z 23 17 21 = (-463853616213487500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_17_21

theorem source_gram_23_17_23 : Z 23 17 23 = (-591705705388297500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_17_23

theorem source_gram_23_19_19 : Z 23 19 19 = (2530981340232345000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_19_19

theorem source_gram_23_19_21 : Z 23 19 21 = (-414739703908530000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_19_21

theorem source_gram_23_19_23 : Z 23 19 23 = (-394470470258865000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_19_23

theorem source_gram_23_21_21 : Z 23 21 21 = (101850365435360416875 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_21_21

theorem source_gram_23_21_23 : Z 23 21 23 = (-246544043911790625 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_21_23

theorem source_gram_23_23_23 : Z 23 23 23 = (25851868812458629565625 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_23_23

theorem source_gram_23_3_1 : Z 23 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_3

theorem source_gram_23_5_1 : Z 23 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_5

theorem source_gram_23_5_3 : Z 23 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_5

theorem source_gram_23_7_1 : Z 23 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_7

theorem source_gram_23_7_3 : Z 23 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_7

theorem source_gram_23_7_5 : Z 23 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_7

theorem source_gram_23_9_1 : Z 23 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_9

theorem source_gram_23_9_3 : Z 23 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_9

theorem source_gram_23_9_5 : Z 23 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_9

theorem source_gram_23_9_7 : Z 23 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_7_9

theorem source_gram_23_11_1 : Z 23 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_11

theorem source_gram_23_11_3 : Z 23 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_11

theorem source_gram_23_11_5 : Z 23 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_11

theorem source_gram_23_11_7 : Z 23 11 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_7_11

theorem source_gram_23_11_9 : Z 23 11 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_9_11

theorem source_gram_23_13_1 : Z 23 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_13

theorem source_gram_23_13_3 : Z 23 13 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_13

theorem source_gram_23_13_5 : Z 23 13 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_13

theorem source_gram_23_13_7 : Z 23 13 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_7_13

theorem source_gram_23_13_9 : Z 23 13 9 = (-308938069440000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_9_13

theorem source_gram_23_13_11 : Z 23 13 11 = (-4854741091200000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_11_13

theorem source_gram_23_15_1 : Z 23 15 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_15

theorem source_gram_23_15_3 : Z 23 15 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_15

theorem source_gram_23_15_5 : Z 23 15 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_15

theorem source_gram_23_15_7 : Z 23 15 7 = (-823834851840000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_7_15

theorem source_gram_23_15_9 : Z 23 15 9 = (-8341327874880000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_9_15

theorem source_gram_23_15_11 : Z 23 15 11 = (-16991593819200000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_11_15

theorem source_gram_23_15_13 : Z 23 15 13 = (-11044535982480000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_13_15

theorem source_gram_23_17_1 : Z 23 17 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_17

theorem source_gram_23_17_3 : Z 23 17 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_17

theorem source_gram_23_17_5 : Z 23 17 5 = (-4501669011840000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_17

theorem source_gram_23_17_7 : Z 23 17 7 = (-24509086842240000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_7_17

theorem source_gram_23_17_9 : Z 23 17 9 = (-26259735902400000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_9_17

theorem source_gram_23_17_11 : Z 23 17 11 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_11_17

theorem source_gram_23_17_13 : Z 23 17 13 = (13411222264440000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_13_17

theorem source_gram_23_17_15 : Z 23 17 15 = (-31292851950360000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_15_17

theorem source_gram_23_19_1 : Z 23 19 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_19

theorem source_gram_23_19_3 : Z 23 19 3 = (-57021140816640000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_19

theorem source_gram_23_19_5 : Z 23 19 5 = (-114042281633280000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_19

theorem source_gram_23_19_7 : Z 23 19 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_7_19

theorem source_gram_23_19_9 : Z 23 19 9 = (119744395714944000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_9_19

theorem source_gram_23_19_11 : Z 23 19 11 = (117606102934320000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_11_19

theorem source_gram_23_19_13 : Z 23 19 13 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_13_19

theorem source_gram_23_19_15 : Z 23 19 15 = (-162153869197320000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_15_19

theorem source_gram_23_19_17 : Z 23 19 17 = (-302924810588400000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_17_19

theorem source_gram_23_21_1 : Z 23 21 1 = (-2195313921440640000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_21

theorem source_gram_23_21_3 : Z 23 21 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_21

theorem source_gram_23_21_5 : Z 23 21 5 = (1746272437509600000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_21

theorem source_gram_23_21_7 : Z 23 21 7 = (1746272437509600000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_7_21

theorem source_gram_23_21_9 : Z 23 21 9 = (1010343338844840000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_9_21

theorem source_gram_23_21_11 : Z 23 21 11 = (274414240180080000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_11_21

theorem source_gram_23_21_13 : Z 23 21 13 = (-202692336496650000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_13_21

theorem source_gram_23_21_15 : Z 23 21 15 = (-420976391185350000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_15_21

theorem source_gram_23_21_17 : Z 23 21 17 = (-463853616213487500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_17_21

theorem source_gram_23_21_19 : Z 23 21 19 = (-414739703908530000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_19_21

theorem source_gram_23_23_1 : Z 23 23 1 = (252461100965673600000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_1_23

theorem source_gram_23_23_3 : Z 23 23 3 = (100984440386269440000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_3_23

theorem source_gram_23_23_5 : Z 23 23 5 = (37869165144851040000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_23

theorem source_gram_23_23_7 : Z 23 23 7 = (12623055048283680000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_7_23

theorem source_gram_23_23_9 : Z 23 23 9 = (3155763762070920000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_9_23

theorem source_gram_23_23_11 : Z 23 23 11 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_11_23

theorem source_gram_23_23_13 : Z 23 23 13 = (-788940940517730000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_13_23

theorem source_gram_23_23_15 : Z 23 23 15 = (-788940940517730000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_15_23

theorem source_gram_23_23_17 : Z 23 23 17 = (-591705705388297500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_17_23

theorem source_gram_23_23_19 : Z 23 23 19 = (-394470470258865000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_19_23

theorem source_gram_23_23_21 : Z 23 23 21 = (-246544043911790625 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_21_23

theorem gram_23 : gramRational 23 = candidateZ_23 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_23_1_1
  · exact source_gram_23_1_3
  · exact source_gram_23_1_5
  · exact source_gram_23_1_7
  · exact source_gram_23_1_9
  · exact source_gram_23_1_11
  · exact source_gram_23_1_13
  · exact source_gram_23_1_15
  · exact source_gram_23_1_17
  · exact source_gram_23_1_19
  · exact source_gram_23_1_21
  · exact source_gram_23_1_23
  · exact source_gram_23_3_1
  · exact source_gram_23_3_3
  · exact source_gram_23_3_5
  · exact source_gram_23_3_7
  · exact source_gram_23_3_9
  · exact source_gram_23_3_11
  · exact source_gram_23_3_13
  · exact source_gram_23_3_15
  · exact source_gram_23_3_17
  · exact source_gram_23_3_19
  · exact source_gram_23_3_21
  · exact source_gram_23_3_23
  · exact source_gram_23_5_1
  · exact source_gram_23_5_3
  · exact source_gram_23_5_5
  · exact source_gram_23_5_7
  · exact source_gram_23_5_9
  · exact source_gram_23_5_11
  · exact source_gram_23_5_13
  · exact source_gram_23_5_15
  · exact source_gram_23_5_17
  · exact source_gram_23_5_19
  · exact source_gram_23_5_21
  · exact source_gram_23_5_23
  · exact source_gram_23_7_1
  · exact source_gram_23_7_3
  · exact source_gram_23_7_5
  · exact source_gram_23_7_7
  · exact source_gram_23_7_9
  · exact source_gram_23_7_11
  · exact source_gram_23_7_13
  · exact source_gram_23_7_15
  · exact source_gram_23_7_17
  · exact source_gram_23_7_19
  · exact source_gram_23_7_21
  · exact source_gram_23_7_23
  · exact source_gram_23_9_1
  · exact source_gram_23_9_3
  · exact source_gram_23_9_5
  · exact source_gram_23_9_7
  · exact source_gram_23_9_9
  · exact source_gram_23_9_11
  · exact source_gram_23_9_13
  · exact source_gram_23_9_15
  · exact source_gram_23_9_17
  · exact source_gram_23_9_19
  · exact source_gram_23_9_21
  · exact source_gram_23_9_23
  · exact source_gram_23_11_1
  · exact source_gram_23_11_3
  · exact source_gram_23_11_5
  · exact source_gram_23_11_7
  · exact source_gram_23_11_9
  · exact source_gram_23_11_11
  · exact source_gram_23_11_13
  · exact source_gram_23_11_15
  · exact source_gram_23_11_17
  · exact source_gram_23_11_19
  · exact source_gram_23_11_21
  · exact source_gram_23_11_23
  · exact source_gram_23_13_1
  · exact source_gram_23_13_3
  · exact source_gram_23_13_5
  · exact source_gram_23_13_7
  · exact source_gram_23_13_9
  · exact source_gram_23_13_11
  · exact source_gram_23_13_13
  · exact source_gram_23_13_15
  · exact source_gram_23_13_17
  · exact source_gram_23_13_19
  · exact source_gram_23_13_21
  · exact source_gram_23_13_23
  · exact source_gram_23_15_1
  · exact source_gram_23_15_3
  · exact source_gram_23_15_5
  · exact source_gram_23_15_7
  · exact source_gram_23_15_9
  · exact source_gram_23_15_11
  · exact source_gram_23_15_13
  · exact source_gram_23_15_15
  · exact source_gram_23_15_17
  · exact source_gram_23_15_19
  · exact source_gram_23_15_21
  · exact source_gram_23_15_23
  · exact source_gram_23_17_1
  · exact source_gram_23_17_3
  · exact source_gram_23_17_5
  · exact source_gram_23_17_7
  · exact source_gram_23_17_9
  · exact source_gram_23_17_11
  · exact source_gram_23_17_13
  · exact source_gram_23_17_15
  · exact source_gram_23_17_17
  · exact source_gram_23_17_19
  · exact source_gram_23_17_21
  · exact source_gram_23_17_23
  · exact source_gram_23_19_1
  · exact source_gram_23_19_3
  · exact source_gram_23_19_5
  · exact source_gram_23_19_7
  · exact source_gram_23_19_9
  · exact source_gram_23_19_11
  · exact source_gram_23_19_13
  · exact source_gram_23_19_15
  · exact source_gram_23_19_17
  · exact source_gram_23_19_19
  · exact source_gram_23_19_21
  · exact source_gram_23_19_23
  · exact source_gram_23_21_1
  · exact source_gram_23_21_3
  · exact source_gram_23_21_5
  · exact source_gram_23_21_7
  · exact source_gram_23_21_9
  · exact source_gram_23_21_11
  · exact source_gram_23_21_13
  · exact source_gram_23_21_15
  · exact source_gram_23_21_17
  · exact source_gram_23_21_19
  · exact source_gram_23_21_21
  · exact source_gram_23_21_23
  · exact source_gram_23_23_1
  · exact source_gram_23_23_3
  · exact source_gram_23_23_5
  · exact source_gram_23_23_7
  · exact source_gram_23_23_9
  · exact source_gram_23_23_11
  · exact source_gram_23_23_13
  · exact source_gram_23_23_15
  · exact source_gram_23_23_17
  · exact source_gram_23_23_19
  · exact source_gram_23_23_21
  · exact source_gram_23_23_23

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_23 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 =
    lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_23_0_0
  · exact computeLDL_23_0_1
  · exact computeLDL_23_0_2
  · exact computeLDL_23_0_3
  · exact computeLDL_23_0_4
  · exact computeLDL_23_0_5
  · exact computeLDL_23_0_6
  · exact computeLDL_23_0_7
  · exact computeLDL_23_0_8
  · exact computeLDL_23_0_9
  · exact computeLDL_23_0_10
  · exact computeLDL_23_0_11
  · exact computeLDL_23_1_0
  · exact computeLDL_23_1_1
  · exact computeLDL_23_1_2
  · exact computeLDL_23_1_3
  · exact computeLDL_23_1_4
  · exact computeLDL_23_1_5
  · exact computeLDL_23_1_6
  · exact computeLDL_23_1_7
  · exact computeLDL_23_1_8
  · exact computeLDL_23_1_9
  · exact computeLDL_23_1_10
  · exact computeLDL_23_1_11
  · exact computeLDL_23_2_0
  · exact computeLDL_23_2_1
  · exact computeLDL_23_2_2
  · exact computeLDL_23_2_3
  · exact computeLDL_23_2_4
  · exact computeLDL_23_2_5
  · exact computeLDL_23_2_6
  · exact computeLDL_23_2_7
  · exact computeLDL_23_2_8
  · exact computeLDL_23_2_9
  · exact computeLDL_23_2_10
  · exact computeLDL_23_2_11
  · exact computeLDL_23_3_0
  · exact computeLDL_23_3_1
  · exact computeLDL_23_3_2
  · exact computeLDL_23_3_3
  · exact computeLDL_23_3_4
  · exact computeLDL_23_3_5
  · exact computeLDL_23_3_6
  · exact computeLDL_23_3_7
  · exact computeLDL_23_3_8
  · exact computeLDL_23_3_9
  · exact computeLDL_23_3_10
  · exact computeLDL_23_3_11
  · exact computeLDL_23_4_0
  · exact computeLDL_23_4_1
  · exact computeLDL_23_4_2
  · exact computeLDL_23_4_3
  · exact computeLDL_23_4_4
  · exact computeLDL_23_4_5
  · exact computeLDL_23_4_6
  · exact computeLDL_23_4_7
  · exact computeLDL_23_4_8
  · exact computeLDL_23_4_9
  · exact computeLDL_23_4_10
  · exact computeLDL_23_4_11
  · exact computeLDL_23_5_0
  · exact computeLDL_23_5_1
  · exact computeLDL_23_5_2
  · exact computeLDL_23_5_3
  · exact computeLDL_23_5_4
  · exact computeLDL_23_5_5
  · exact computeLDL_23_5_6
  · exact computeLDL_23_5_7
  · exact computeLDL_23_5_8
  · exact computeLDL_23_5_9
  · exact computeLDL_23_5_10
  · exact computeLDL_23_5_11
  · exact computeLDL_23_6_0
  · exact computeLDL_23_6_1
  · exact computeLDL_23_6_2
  · exact computeLDL_23_6_3
  · exact computeLDL_23_6_4
  · exact computeLDL_23_6_5
  · exact computeLDL_23_6_6
  · exact computeLDL_23_6_7
  · exact computeLDL_23_6_8
  · exact computeLDL_23_6_9
  · exact computeLDL_23_6_10
  · exact computeLDL_23_6_11
  · exact computeLDL_23_7_0
  · exact computeLDL_23_7_1
  · exact computeLDL_23_7_2
  · exact computeLDL_23_7_3
  · exact computeLDL_23_7_4
  · exact computeLDL_23_7_5
  · exact computeLDL_23_7_6
  · exact computeLDL_23_7_7
  · exact computeLDL_23_7_8
  · exact computeLDL_23_7_9
  · exact computeLDL_23_7_10
  · exact computeLDL_23_7_11
  · exact computeLDL_23_8_0
  · exact computeLDL_23_8_1
  · exact computeLDL_23_8_2
  · exact computeLDL_23_8_3
  · exact computeLDL_23_8_4
  · exact computeLDL_23_8_5
  · exact computeLDL_23_8_6
  · exact computeLDL_23_8_7
  · exact computeLDL_23_8_8
  · exact computeLDL_23_8_9
  · exact computeLDL_23_8_10
  · exact computeLDL_23_8_11
  · exact computeLDL_23_9_0
  · exact computeLDL_23_9_1
  · exact computeLDL_23_9_2
  · exact computeLDL_23_9_3
  · exact computeLDL_23_9_4
  · exact computeLDL_23_9_5
  · exact computeLDL_23_9_6
  · exact computeLDL_23_9_7
  · exact computeLDL_23_9_8
  · exact computeLDL_23_9_9
  · exact computeLDL_23_9_10
  · exact computeLDL_23_9_11
  · exact computeLDL_23_10_0
  · exact computeLDL_23_10_1
  · exact computeLDL_23_10_2
  · exact computeLDL_23_10_3
  · exact computeLDL_23_10_4
  · exact computeLDL_23_10_5
  · exact computeLDL_23_10_6
  · exact computeLDL_23_10_7
  · exact computeLDL_23_10_8
  · exact computeLDL_23_10_9
  · exact computeLDL_23_10_10
  · exact computeLDL_23_10_11
  · exact computeLDL_23_11_0
  · exact computeLDL_23_11_1
  · exact computeLDL_23_11_2
  · exact computeLDL_23_11_3
  · exact computeLDL_23_11_4
  · exact computeLDL_23_11_5
  · exact computeLDL_23_11_6
  · exact computeLDL_23_11_7
  · exact computeLDL_23_11_8
  · exact computeLDL_23_11_9
  · exact computeLDL_23_11_10
  · exact computeLDL_23_11_11

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_23_oai : compressedRational 23 =
    lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose := by
  rw [compressedRational_eq_compute, error_23, gram_23]
  exact candidateLDL_23

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_23_oai := @OAI.Laughlin.Certificate.ldl_23_oai
