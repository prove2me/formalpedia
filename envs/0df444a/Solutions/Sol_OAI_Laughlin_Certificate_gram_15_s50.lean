-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_15_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:10:09.53974+00:00
-- url     : https://prove2.me/submissions/5fc90b56-4165-4125-804c-c0031373b1a3

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_11_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_11_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_11_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_11_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_11_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_13_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_13_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_13_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_13_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_13_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_13_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_15_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_15_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_15_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_15_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_15_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_15_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_15_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_15_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_15 : GramCompute.quadruples 15 = [(0,1,2,13), (0,1,3,12), (0,1,4,11), (0,1,5,10), (0,1,6,9), (0,1,7,8), (0,2,3,11), (0,2,4,10), (0,2,5,9), (0,2,6,8), (0,3,4,9), (0,3,5,8), (0,3,6,7), (0,4,5,7), (1,2,3,10), (1,2,4,9), (1,2,5,8), (1,2,6,7), (1,3,4,8), (1,3,5,7), (1,4,5,6), (2,3,4,7), (2,3,5,6)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram01Batch15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_15_1_1 : GramCompute.ZFast 15 1 1 = (174356582400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_1_3 : GramCompute.ZFast 15 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_1_5 : GramCompute.ZFast 15 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_1_7 : GramCompute.ZFast 15 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_1_9 : GramCompute.ZFast 15 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_1_11 : GramCompute.ZFast 15 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_1_13 : GramCompute.ZFast 15 1 13 = (-2724321600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_1_15 : GramCompute.ZFast 15 1 15 = (122594472000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram03Batch15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_15_3_3 : GramCompute.ZFast 15 3 3 = (2874009600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_3_5 : GramCompute.ZFast 15 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_3_7 : GramCompute.ZFast 15 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_3_9 : GramCompute.ZFast 15 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_3_11 : GramCompute.ZFast 15 3 11 = (-179625600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_3_13 : GramCompute.ZFast 15 3 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_15_1_1 : Z 15 1 1 = (174356582400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_1

theorem source_gram_15_1_3 : Z 15 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_3

theorem source_gram_15_1_5 : Z 15 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_5

theorem source_gram_15_1_7 : Z 15 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_7

theorem source_gram_15_1_9 : Z 15 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_9

theorem source_gram_15_1_11 : Z 15 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_11

theorem source_gram_15_1_13 : Z 15 1 13 = (-2724321600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_13

theorem source_gram_15_1_15 : Z 15 1 15 = (122594472000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_15

theorem source_gram_15_3_3 : Z 15 3 3 = (2874009600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_3

theorem source_gram_15_3_5 : Z 15 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_5

theorem source_gram_15_3_7 : Z 15 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_7

theorem source_gram_15_3_9 : Z 15 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_9

theorem source_gram_15_3_11 : Z 15 3 11 = (-179625600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_11

theorem source_gram_15_3_13 : Z 15 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_13

theorem gram_15_s50_oai : gramRational 15 = candidateZ_15 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_15_1_1
  · exact source_gram_15_1_3
  · exact source_gram_15_1_5
  · exact source_gram_15_1_7
  · exact source_gram_15_1_9
  · exact source_gram_15_1_11
  · exact source_gram_15_1_13
  · exact source_gram_15_1_15
  · exact source_gram_15_3_1_s50
  · exact source_gram_15_3_3
  · exact source_gram_15_3_5
  · exact source_gram_15_3_7
  · exact source_gram_15_3_9
  · exact source_gram_15_3_11
  · exact source_gram_15_3_13
  · exact source_gram_15_3_15_s50
  · exact source_gram_15_5_1_s50
  · exact source_gram_15_5_3_s50
  · exact source_gram_15_5_5_s50
  · exact source_gram_15_5_7_s50
  · exact source_gram_15_5_9_s50
  · exact source_gram_15_5_11_s50
  · exact source_gram_15_5_13_s50
  · exact source_gram_15_5_15_s50
  · exact source_gram_15_7_1_s50
  · exact source_gram_15_7_3_s50
  · exact source_gram_15_7_5_s50
  · exact source_gram_15_7_7_s50
  · exact source_gram_15_7_9_s50
  · exact source_gram_15_7_11_s50
  · exact source_gram_15_7_13_s50
  · exact source_gram_15_7_15_s50
  · exact source_gram_15_9_1_s50
  · exact source_gram_15_9_3_s50
  · exact source_gram_15_9_5_s50
  · exact source_gram_15_9_7_s50
  · exact source_gram_15_9_9_s50
  · exact source_gram_15_9_11_s50
  · exact source_gram_15_9_13_s50
  · exact source_gram_15_9_15_s50
  · exact source_gram_15_11_1_s50
  · exact source_gram_15_11_3_s50
  · exact source_gram_15_11_5_s50
  · exact source_gram_15_11_7_s50
  · exact source_gram_15_11_9_s50
  · exact source_gram_15_11_11_s50
  · exact source_gram_15_11_13_s50
  · exact source_gram_15_11_15_s50
  · exact source_gram_15_13_1_s50
  · exact source_gram_15_13_3_s50
  · exact source_gram_15_13_5_s50
  · exact source_gram_15_13_7_s50
  · exact source_gram_15_13_9_s50
  · exact source_gram_15_13_11_s50
  · exact source_gram_15_13_13_s50
  · exact source_gram_15_13_15_s50
  · exact source_gram_15_15_1_s50
  · exact source_gram_15_15_3_s50
  · exact source_gram_15_15_5_s50
  · exact source_gram_15_15_7_s50
  · exact source_gram_15_15_9_s50
  · exact source_gram_15_15_11_s50
  · exact source_gram_15_15_13_s50
  · exact source_gram_15_15_15_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_15_s50_oai := @OAI.Laughlin.Certificate.gram_15_s50_oai
