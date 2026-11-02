-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_12_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:07:44.834512+00:00
-- url     : https://prove2.me/submissions/d4c0b792-c710-4813-adb3-be987300172e

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_11_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_11_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_11_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_11_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_11_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_12 : GramCompute.quadruples 12 = [(0,1,2,10), (0,1,3,9), (0,1,4,8), (0,1,5,7), (0,2,3,8), (0,2,4,7), (0,2,5,6), (0,3,4,6), (1,2,3,7), (1,2,4,6), (1,3,4,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram01Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_1_1 : GramCompute.ZFast 12 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_3 : GramCompute.ZFast 12 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_5 : GramCompute.ZFast 12 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_7 : GramCompute.ZFast 12 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_9 : GramCompute.ZFast 12 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_1_11 : GramCompute.ZFast 12 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram03Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_3_3 : GramCompute.ZFast 12 3 3 = (2177280 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_5 : GramCompute.ZFast 12 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_7 : GramCompute.ZFast 12 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_9 : GramCompute.ZFast 12 3 9 = (-1088640 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_12_1_1 : Z 12 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_1

theorem source_gram_12_1_3 : Z 12 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_3

theorem source_gram_12_1_5 : Z 12 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_5

theorem source_gram_12_1_7 : Z 12 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_7

theorem source_gram_12_1_9 : Z 12 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_9

theorem source_gram_12_1_11 : Z 12 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_11

theorem source_gram_12_3_3 : Z 12 3 3 = (2177280 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_3

theorem source_gram_12_3_5 : Z 12 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_5

theorem source_gram_12_3_7 : Z 12 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_7

theorem source_gram_12_3_9 : Z 12 3 9 = (-1088640 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_9

theorem gram_12_s50_oai : gramRational 12 = candidateZ_12 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_12_1_1
  · exact source_gram_12_1_3
  · exact source_gram_12_1_5
  · exact source_gram_12_1_7
  · exact source_gram_12_1_9
  · exact source_gram_12_1_11
  · exact source_gram_12_3_1_s50
  · exact source_gram_12_3_3
  · exact source_gram_12_3_5
  · exact source_gram_12_3_7
  · exact source_gram_12_3_9
  · exact source_gram_12_3_11_s50
  · exact source_gram_12_5_1_s50
  · exact source_gram_12_5_3_s50
  · exact source_gram_12_5_5_s50
  · exact source_gram_12_5_7_s50
  · exact source_gram_12_5_9_s50
  · exact source_gram_12_5_11_s50
  · exact source_gram_12_7_1_s50
  · exact source_gram_12_7_3_s50
  · exact source_gram_12_7_5_s50
  · exact source_gram_12_7_7_s50
  · exact source_gram_12_7_9_s50
  · exact source_gram_12_7_11_s50
  · exact source_gram_12_9_1_s50
  · exact source_gram_12_9_3_s50
  · exact source_gram_12_9_5_s50
  · exact source_gram_12_9_7_s50
  · exact source_gram_12_9_9_s50
  · exact source_gram_12_9_11_s50
  · exact source_gram_12_11_1_s50
  · exact source_gram_12_11_3_s50
  · exact source_gram_12_11_5_s50
  · exact source_gram_12_11_7_s50
  · exact source_gram_12_11_9_s50
  · exact source_gram_12_11_11_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_12_s50_oai := @OAI.Laughlin.Certificate.gram_12_s50_oai
