-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_22_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:16:58.569417+00:00
-- url     : https://prove2.me/submissions/2d314567-03a0-4277-91bb-073eae4d3cd4

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_11_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_13_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_15_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_17_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_19_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_21_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_3_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_3_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_22_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_22 : GramCompute.quadruples 22 = [(0,1,2,20), (0,1,3,19), (0,1,4,18), (0,1,5,17), (0,1,6,16), (0,1,7,15), (0,1,8,14), (0,1,9,13), (0,1,10,12), (0,2,3,18), (0,2,4,17), (0,2,5,16), (0,2,6,15), (0,2,7,14), (0,2,8,13), (0,2,9,12), (0,2,10,11), (0,3,4,16), (0,3,5,15), (0,3,6,14), (0,3,7,13), (0,3,8,12), (0,3,9,11), (0,4,5,14), (0,4,6,13), (0,4,7,12), (0,4,8,11), (0,4,9,10), (0,5,6,12), (0,5,7,11), (0,5,8,10), (0,6,7,10), (0,6,8,9), (1,2,3,17), (1,2,4,16), (1,2,5,15), (1,2,6,14), (1,2,7,13), (1,2,8,12), (1,2,9,11), (1,3,4,15), (1,3,5,14), (1,3,6,13), (1,3,7,12), (1,3,8,11), (1,3,9,10), (1,4,5,13), (1,4,6,12), (1,4,7,11), (1,4,8,10), (1,5,6,11), (1,5,7,10), (1,5,8,9), (1,6,7,9), (2,3,4,14), (2,3,5,13), (2,3,6,12), (2,3,7,11), (2,3,8,10), (2,4,5,12), (2,4,6,11), (2,4,7,10), (2,4,8,9), (2,5,6,10), (2,5,7,9), (2,6,7,8), (3,4,5,11), (3,4,6,10), (3,4,7,9), (3,5,6,9), (3,5,7,8), (4,5,6,8)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram01Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_1_1 : GramCompute.ZFast 22 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_3 : GramCompute.ZFast 22 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_5 : GramCompute.ZFast 22 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_7 : GramCompute.ZFast 22 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_9 : GramCompute.ZFast 22 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_11 : GramCompute.ZFast 22 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_13 : GramCompute.ZFast 22 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_15 : GramCompute.ZFast 22 1 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_17 : GramCompute.ZFast 22 1 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_19 : GramCompute.ZFast 22 1 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_21 : GramCompute.ZFast 22 1 21 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram03Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeGram_22_3_5 : GramCompute.ZFast 22 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_7 : GramCompute.ZFast 22 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_9 : GramCompute.ZFast 22 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_11 : GramCompute.ZFast 22 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_13 : GramCompute.ZFast 22 3 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_15 : GramCompute.ZFast 22 3 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_17 : GramCompute.ZFast 22 3 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram05Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeGram_22_5_7 : GramCompute.ZFast 22 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_22_1_1 : Z 22 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_1

theorem source_gram_22_1_3 : Z 22 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_3

theorem source_gram_22_1_5 : Z 22 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_5

theorem source_gram_22_1_7 : Z 22 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_7

theorem source_gram_22_1_9 : Z 22 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_9

theorem source_gram_22_1_11 : Z 22 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_11

theorem source_gram_22_1_13 : Z 22 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_13

theorem source_gram_22_1_15 : Z 22 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_15

theorem source_gram_22_1_17 : Z 22 1 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_17

theorem source_gram_22_1_19 : Z 22 1 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_19

theorem source_gram_22_1_21 : Z 22 1 21 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_21

theorem source_gram_22_3_5 : Z 22 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_5

theorem source_gram_22_3_7 : Z 22 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_7

theorem source_gram_22_3_9 : Z 22 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_9

theorem source_gram_22_3_11 : Z 22 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_11

theorem source_gram_22_3_13 : Z 22 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_13

theorem source_gram_22_3_15 : Z 22 3 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_15

theorem source_gram_22_3_17 : Z 22 3 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_17

theorem source_gram_22_5_7 : Z 22 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_7

theorem gram_22_s50_oai : gramRational 22 = candidateZ_22 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_22_1_1
  · exact source_gram_22_1_3
  · exact source_gram_22_1_5
  · exact source_gram_22_1_7
  · exact source_gram_22_1_9
  · exact source_gram_22_1_11
  · exact source_gram_22_1_13
  · exact source_gram_22_1_15
  · exact source_gram_22_1_17
  · exact source_gram_22_1_19
  · exact source_gram_22_1_21
  · exact source_gram_22_3_1_s50
  · exact source_gram_22_3_3_s50
  · exact source_gram_22_3_5
  · exact source_gram_22_3_7
  · exact source_gram_22_3_9
  · exact source_gram_22_3_11
  · exact source_gram_22_3_13
  · exact source_gram_22_3_15
  · exact source_gram_22_3_17
  · exact source_gram_22_3_19_s50
  · exact source_gram_22_3_21_s50
  · exact source_gram_22_5_1_s50
  · exact source_gram_22_5_3_s50
  · exact source_gram_22_5_5_s50
  · exact source_gram_22_5_7
  · exact source_gram_22_5_9_s50
  · exact source_gram_22_5_11_s50
  · exact source_gram_22_5_13_s50
  · exact source_gram_22_5_15_s50
  · exact source_gram_22_5_17_s50
  · exact source_gram_22_5_19_s50
  · exact source_gram_22_5_21_s50
  · exact source_gram_22_7_1_s50
  · exact source_gram_22_7_3_s50
  · exact source_gram_22_7_5_s50
  · exact source_gram_22_7_7_s50
  · exact source_gram_22_7_9_s50
  · exact source_gram_22_7_11_s50
  · exact source_gram_22_7_13_s50
  · exact source_gram_22_7_15_s50
  · exact source_gram_22_7_17_s50
  · exact source_gram_22_7_19_s50
  · exact source_gram_22_7_21_s50
  · exact source_gram_22_9_1_s50
  · exact source_gram_22_9_3_s50
  · exact source_gram_22_9_5_s50
  · exact source_gram_22_9_7_s50
  · exact source_gram_22_9_9_s50
  · exact source_gram_22_9_11_s50
  · exact source_gram_22_9_13_s50
  · exact source_gram_22_9_15_s50
  · exact source_gram_22_9_17_s50
  · exact source_gram_22_9_19_s50
  · exact source_gram_22_9_21_s50
  · exact source_gram_22_11_1_s50
  · exact source_gram_22_11_3_s50
  · exact source_gram_22_11_5_s50
  · exact source_gram_22_11_7_s50
  · exact source_gram_22_11_9_s50
  · exact source_gram_22_11_11_s50
  · exact source_gram_22_11_13_s50
  · exact source_gram_22_11_15_s50
  · exact source_gram_22_11_17_s50
  · exact source_gram_22_11_19_s50
  · exact source_gram_22_11_21_s50
  · exact source_gram_22_13_1_s50
  · exact source_gram_22_13_3_s50
  · exact source_gram_22_13_5_s50
  · exact source_gram_22_13_7_s50
  · exact source_gram_22_13_9_s50
  · exact source_gram_22_13_11_s50
  · exact source_gram_22_13_13_s50
  · exact source_gram_22_13_15_s50
  · exact source_gram_22_13_17_s50
  · exact source_gram_22_13_19_s50
  · exact source_gram_22_13_21_s50
  · exact source_gram_22_15_1_s50
  · exact source_gram_22_15_3_s50
  · exact source_gram_22_15_5_s50
  · exact source_gram_22_15_7_s50
  · exact source_gram_22_15_9_s50
  · exact source_gram_22_15_11_s50
  · exact source_gram_22_15_13_s50
  · exact source_gram_22_15_15_s50
  · exact source_gram_22_15_17_s50
  · exact source_gram_22_15_19_s50
  · exact source_gram_22_15_21_s50
  · exact source_gram_22_17_1_s50
  · exact source_gram_22_17_3_s50
  · exact source_gram_22_17_5_s50
  · exact source_gram_22_17_7_s50
  · exact source_gram_22_17_9_s50
  · exact source_gram_22_17_11_s50
  · exact source_gram_22_17_13_s50
  · exact source_gram_22_17_15_s50
  · exact source_gram_22_17_17_s50
  · exact source_gram_22_17_19_s50
  · exact source_gram_22_17_21_s50
  · exact source_gram_22_19_1_s50
  · exact source_gram_22_19_3_s50
  · exact source_gram_22_19_5_s50
  · exact source_gram_22_19_7_s50
  · exact source_gram_22_19_9_s50
  · exact source_gram_22_19_11_s50
  · exact source_gram_22_19_13_s50
  · exact source_gram_22_19_15_s50
  · exact source_gram_22_19_17_s50
  · exact source_gram_22_19_19_s50
  · exact source_gram_22_19_21_s50
  · exact source_gram_22_21_1_s50
  · exact source_gram_22_21_3_s50
  · exact source_gram_22_21_5_s50
  · exact source_gram_22_21_7_s50
  · exact source_gram_22_21_9_s50
  · exact source_gram_22_21_11_s50
  · exact source_gram_22_21_13_s50
  · exact source_gram_22_21_15_s50
  · exact source_gram_22_21_17_s50
  · exact source_gram_22_21_19_s50
  · exact source_gram_22_21_21_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_22_s50_oai := @OAI.Laughlin.Certificate.gram_22_s50_oai
