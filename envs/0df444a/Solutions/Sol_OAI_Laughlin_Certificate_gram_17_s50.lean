-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:11:22.953343+00:00
-- url     : https://prove2.me/submissions/6ef71c4b-2f8e-4d3a-8ed3-e4af738294a7

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_11_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_15_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_17_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_3_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_17 : GramCompute.quadruples 17 = [(0,1,2,15), (0,1,3,14), (0,1,4,13), (0,1,5,12), (0,1,6,11), (0,1,7,10), (0,1,8,9), (0,2,3,13), (0,2,4,12), (0,2,5,11), (0,2,6,10), (0,2,7,9), (0,3,4,11), (0,3,5,10), (0,3,6,9), (0,3,7,8), (0,4,5,9), (0,4,6,8), (0,5,6,7), (1,2,3,12), (1,2,4,11), (1,2,5,10), (1,2,6,9), (1,2,7,8), (1,3,4,10), (1,3,5,9), (1,3,6,8), (1,4,5,8), (1,4,6,7), (2,3,4,9), (2,3,5,8), (2,3,6,7), (2,4,5,7), (3,4,5,6)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram01Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_17_1_1 : GramCompute.ZFast 17 1 1 = (41845579776000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_1_3 : GramCompute.ZFast 17 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_1_5 : GramCompute.ZFast 17 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_1_7 : GramCompute.ZFast 17 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_1_9 : GramCompute.ZFast 17 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_1_11 : GramCompute.ZFast 17 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_1_13 : GramCompute.ZFast 17 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_1_15 : GramCompute.ZFast 17 1 15 = (-326918592000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_1_17 : GramCompute.ZFast 17 1 17 = (19451656224000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram03Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_17_3_3 : GramCompute.ZFast 17 3 3 = (523069747200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_3_5 : GramCompute.ZFast 17 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_3_7 : GramCompute.ZFast 17 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_3_9 : GramCompute.ZFast 17 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_3_11 : GramCompute.ZFast 17 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_3_13 : GramCompute.ZFast 17 3 13 = (-16345929600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_3_15 : GramCompute.ZFast 17 3 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_FastChoose
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_NumericBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem Z_eq_gramCompute (D r s : ℕ) : Z D r s = GramCompute.ZFast D r s := by
  exact Z_eq_fast D r s

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_17_1_1 : Z 17 1 1 = (41845579776000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_1

theorem source_gram_17_1_3 : Z 17 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_3

theorem source_gram_17_1_5 : Z 17 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_5

theorem source_gram_17_1_7 : Z 17 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_7

theorem source_gram_17_1_9 : Z 17 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_9

theorem source_gram_17_1_11 : Z 17 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_11

theorem source_gram_17_1_13 : Z 17 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_13

theorem source_gram_17_1_15 : Z 17 1 15 = (-326918592000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_15

theorem source_gram_17_1_17 : Z 17 1 17 = (19451656224000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_17

theorem source_gram_17_3_3 : Z 17 3 3 = (523069747200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_3

theorem source_gram_17_3_5 : Z 17 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_5

theorem source_gram_17_3_7 : Z 17 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_7

theorem source_gram_17_3_9 : Z 17 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_9

theorem source_gram_17_3_11 : Z 17 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_11

theorem source_gram_17_3_13 : Z 17 3 13 = (-16345929600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_13

theorem source_gram_17_3_15 : Z 17 3 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_15

theorem gram_17_s50_oai : gramRational 17 = candidateZ_17 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_17_1_1
  · exact source_gram_17_1_3
  · exact source_gram_17_1_5
  · exact source_gram_17_1_7
  · exact source_gram_17_1_9
  · exact source_gram_17_1_11
  · exact source_gram_17_1_13
  · exact source_gram_17_1_15
  · exact source_gram_17_1_17
  · exact source_gram_17_3_1_s50
  · exact source_gram_17_3_3
  · exact source_gram_17_3_5
  · exact source_gram_17_3_7
  · exact source_gram_17_3_9
  · exact source_gram_17_3_11
  · exact source_gram_17_3_13
  · exact source_gram_17_3_15
  · exact source_gram_17_3_17_s50
  · exact source_gram_17_5_1_s50
  · exact source_gram_17_5_3_s50
  · exact source_gram_17_5_5_s50
  · exact source_gram_17_5_7_s50
  · exact source_gram_17_5_9_s50
  · exact source_gram_17_5_11_s50
  · exact source_gram_17_5_13_s50
  · exact source_gram_17_5_15_s50
  · exact source_gram_17_5_17_s50
  · exact source_gram_17_7_1_s50
  · exact source_gram_17_7_3_s50
  · exact source_gram_17_7_5_s50
  · exact source_gram_17_7_7_s50
  · exact source_gram_17_7_9_s50
  · exact source_gram_17_7_11_s50
  · exact source_gram_17_7_13_s50
  · exact source_gram_17_7_15_s50
  · exact source_gram_17_7_17_s50
  · exact source_gram_17_9_1_s50
  · exact source_gram_17_9_3_s50
  · exact source_gram_17_9_5_s50
  · exact source_gram_17_9_7_s50
  · exact source_gram_17_9_9_s50
  · exact source_gram_17_9_11_s50
  · exact source_gram_17_9_13_s50
  · exact source_gram_17_9_15_s50
  · exact source_gram_17_9_17_s50
  · exact source_gram_17_11_1_s50
  · exact source_gram_17_11_3_s50
  · exact source_gram_17_11_5_s50
  · exact source_gram_17_11_7_s50
  · exact source_gram_17_11_9_s50
  · exact source_gram_17_11_11_s50
  · exact source_gram_17_11_13_s50
  · exact source_gram_17_11_15_s50
  · exact source_gram_17_11_17_s50
  · exact source_gram_17_13_1_s50
  · exact source_gram_17_13_3_s50
  · exact source_gram_17_13_5_s50
  · exact source_gram_17_13_7_s50
  · exact source_gram_17_13_9_s50
  · exact source_gram_17_13_11_s50
  · exact source_gram_17_13_13_s50
  · exact source_gram_17_13_15_s50
  · exact source_gram_17_13_17_s50
  · exact source_gram_17_15_1_s50
  · exact source_gram_17_15_3_s50
  · exact source_gram_17_15_5_s50
  · exact source_gram_17_15_7_s50
  · exact source_gram_17_15_9_s50
  · exact source_gram_17_15_11_s50
  · exact source_gram_17_15_13_s50
  · exact source_gram_17_15_15_s50
  · exact source_gram_17_15_17_s50
  · exact source_gram_17_17_1_s50
  · exact source_gram_17_17_3_s50
  · exact source_gram_17_17_5_s50
  · exact source_gram_17_17_7_s50
  · exact source_gram_17_17_9_s50
  · exact source_gram_17_17_11_s50
  · exact source_gram_17_17_13_s50
  · exact source_gram_17_17_15_s50
  · exact source_gram_17_17_17_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_17_s50_oai := @OAI.Laughlin.Certificate.gram_17_s50_oai
