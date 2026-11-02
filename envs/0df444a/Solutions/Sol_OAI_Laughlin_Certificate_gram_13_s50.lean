-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_13_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:08:09.633178+00:00
-- url     : https://prove2.me/submissions/11ae6bd9-3e80-4519-99df-9ba0c696bc5a

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_11_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_11_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_11_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_11_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_11_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_13_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_13_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_13_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_13_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_13_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_13_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_13_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_13 : GramCompute.quadruples 13 = [(0,1,2,11), (0,1,3,10), (0,1,4,9), (0,1,5,8), (0,1,6,7), (0,2,3,9), (0,2,4,8), (0,2,5,7), (0,3,4,7), (0,3,5,6), (1,2,3,8), (1,2,4,7), (1,2,5,6), (1,3,4,6), (2,3,4,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram01Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_1_1 : GramCompute.ZFast 13 1 1 = (958003200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_3 : GramCompute.ZFast 13 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_5 : GramCompute.ZFast 13 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_7 : GramCompute.ZFast 13 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_9 : GramCompute.ZFast 13 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_11 : GramCompute.ZFast 13 1 11 = (-29937600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_1_13 : GramCompute.ZFast 13 1 13 = (972972000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram03Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_3_3 : GramCompute.ZFast 13 3 3 = (21772800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_5 : GramCompute.ZFast 13 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_7 : GramCompute.ZFast 13 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_9 : GramCompute.ZFast 13 3 9 = (-2721600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_3_11 : GramCompute.ZFast 13 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_13_1_1 : Z 13 1 1 = (958003200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_1

theorem source_gram_13_1_3 : Z 13 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_3

theorem source_gram_13_1_5 : Z 13 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_5

theorem source_gram_13_1_7 : Z 13 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_7

theorem source_gram_13_1_9 : Z 13 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_9

theorem source_gram_13_1_11 : Z 13 1 11 = (-29937600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_11

theorem source_gram_13_1_13 : Z 13 1 13 = (972972000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_13

theorem source_gram_13_3_3 : Z 13 3 3 = (21772800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_3

theorem source_gram_13_3_5 : Z 13 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_5

theorem source_gram_13_3_7 : Z 13 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_7

theorem source_gram_13_3_9 : Z 13 3 9 = (-2721600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_9

theorem source_gram_13_3_11 : Z 13 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_11

theorem gram_13_s50_oai : gramRational 13 = candidateZ_13 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_13_1_1
  · exact source_gram_13_1_3
  · exact source_gram_13_1_5
  · exact source_gram_13_1_7
  · exact source_gram_13_1_9
  · exact source_gram_13_1_11
  · exact source_gram_13_1_13
  · exact source_gram_13_3_1_s50
  · exact source_gram_13_3_3
  · exact source_gram_13_3_5
  · exact source_gram_13_3_7
  · exact source_gram_13_3_9
  · exact source_gram_13_3_11
  · exact source_gram_13_3_13_s50
  · exact source_gram_13_5_1_s50
  · exact source_gram_13_5_3_s50
  · exact source_gram_13_5_5_s50
  · exact source_gram_13_5_7_s50
  · exact source_gram_13_5_9_s50
  · exact source_gram_13_5_11_s50
  · exact source_gram_13_5_13_s50
  · exact source_gram_13_7_1_s50
  · exact source_gram_13_7_3_s50
  · exact source_gram_13_7_5_s50
  · exact source_gram_13_7_7_s50
  · exact source_gram_13_7_9_s50
  · exact source_gram_13_7_11_s50
  · exact source_gram_13_7_13_s50
  · exact source_gram_13_9_1_s50
  · exact source_gram_13_9_3_s50
  · exact source_gram_13_9_5_s50
  · exact source_gram_13_9_7_s50
  · exact source_gram_13_9_9_s50
  · exact source_gram_13_9_11_s50
  · exact source_gram_13_9_13_s50
  · exact source_gram_13_11_1_s50
  · exact source_gram_13_11_3_s50
  · exact source_gram_13_11_5_s50
  · exact source_gram_13_11_7_s50
  · exact source_gram_13_11_9_s50
  · exact source_gram_13_11_11_s50
  · exact source_gram_13_11_13_s50
  · exact source_gram_13_13_1_s50
  · exact source_gram_13_13_3_s50
  · exact source_gram_13_13_5_s50
  · exact source_gram_13_13_7_s50
  · exact source_gram_13_13_9_s50
  · exact source_gram_13_13_11_s50
  · exact source_gram_13_13_13_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_13_s50_oai := @OAI.Laughlin.Certificate.gram_13_s50_oai
