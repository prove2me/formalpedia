-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_20_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:14:58.585303+00:00
-- url     : https://prove2.me/submissions/5879879c-1560-4228-a14f-7f921b2cc3d3

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_11_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_13_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_15_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_17_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_19_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_3_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_20_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_20 : GramCompute.quadruples 20 = [(0,1,2,18), (0,1,3,17), (0,1,4,16), (0,1,5,15), (0,1,6,14), (0,1,7,13), (0,1,8,12), (0,1,9,11), (0,2,3,16), (0,2,4,15), (0,2,5,14), (0,2,6,13), (0,2,7,12), (0,2,8,11), (0,2,9,10), (0,3,4,14), (0,3,5,13), (0,3,6,12), (0,3,7,11), (0,3,8,10), (0,4,5,12), (0,4,6,11), (0,4,7,10), (0,4,8,9), (0,5,6,10), (0,5,7,9), (0,6,7,8), (1,2,3,15), (1,2,4,14), (1,2,5,13), (1,2,6,12), (1,2,7,11), (1,2,8,10), (1,3,4,13), (1,3,5,12), (1,3,6,11), (1,3,7,10), (1,3,8,9), (1,4,5,11), (1,4,6,10), (1,4,7,9), (1,5,6,9), (1,5,7,8), (2,3,4,12), (2,3,5,11), (2,3,6,10), (2,3,7,9), (2,4,5,10), (2,4,6,9), (2,4,7,8), (2,5,6,8), (3,4,5,9), (3,4,6,8), (3,5,6,7)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram01Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_1_1 : GramCompute.ZFast 20 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_3 : GramCompute.ZFast 20 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_5 : GramCompute.ZFast 20 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_7 : GramCompute.ZFast 20 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_9 : GramCompute.ZFast 20 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_11 : GramCompute.ZFast 20 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_13 : GramCompute.ZFast 20 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_15 : GramCompute.ZFast 20 1 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_17 : GramCompute.ZFast 20 1 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_1_19 : GramCompute.ZFast 20 1 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram03Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_3_3 : GramCompute.ZFast 20 3 3 = (2134124568576000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_5 : GramCompute.ZFast 20 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_7 : GramCompute.ZFast 20 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_9 : GramCompute.ZFast 20 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_11 : GramCompute.ZFast 20 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_13 : GramCompute.ZFast 20 3 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_15 : GramCompute.ZFast 20 3 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_3_17 : GramCompute.ZFast 20 3 17 = (-133382785536000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_20_1_1 : Z 20 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_1

theorem source_gram_20_1_3 : Z 20 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_3

theorem source_gram_20_1_5 : Z 20 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_5

theorem source_gram_20_1_7 : Z 20 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_7

theorem source_gram_20_1_9 : Z 20 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_9

theorem source_gram_20_1_11 : Z 20 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_11

theorem source_gram_20_1_13 : Z 20 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_13

theorem source_gram_20_1_15 : Z 20 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_15

theorem source_gram_20_1_17 : Z 20 1 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_17

theorem source_gram_20_1_19 : Z 20 1 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_1_19

theorem source_gram_20_3_3 : Z 20 3 3 = (2134124568576000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_3

theorem source_gram_20_3_5 : Z 20 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_5

theorem source_gram_20_3_7 : Z 20 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_7

theorem source_gram_20_3_9 : Z 20 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_9

theorem source_gram_20_3_11 : Z 20 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_11

theorem source_gram_20_3_13 : Z 20 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_13

theorem source_gram_20_3_15 : Z 20 3 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_15

theorem source_gram_20_3_17 : Z 20 3 17 = (-133382785536000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_3_17

theorem gram_20_s50_oai : gramRational 20 = candidateZ_20 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_20_1_1
  · exact source_gram_20_1_3
  · exact source_gram_20_1_5
  · exact source_gram_20_1_7
  · exact source_gram_20_1_9
  · exact source_gram_20_1_11
  · exact source_gram_20_1_13
  · exact source_gram_20_1_15
  · exact source_gram_20_1_17
  · exact source_gram_20_1_19
  · exact source_gram_20_3_1_s50
  · exact source_gram_20_3_3
  · exact source_gram_20_3_5
  · exact source_gram_20_3_7
  · exact source_gram_20_3_9
  · exact source_gram_20_3_11
  · exact source_gram_20_3_13
  · exact source_gram_20_3_15
  · exact source_gram_20_3_17
  · exact source_gram_20_3_19_s50
  · exact source_gram_20_5_1_s50
  · exact source_gram_20_5_3_s50
  · exact source_gram_20_5_5_s50
  · exact source_gram_20_5_7_s50
  · exact source_gram_20_5_9_s50
  · exact source_gram_20_5_11_s50
  · exact source_gram_20_5_13_s50
  · exact source_gram_20_5_15_s50
  · exact source_gram_20_5_17_s50
  · exact source_gram_20_5_19_s50
  · exact source_gram_20_7_1_s50
  · exact source_gram_20_7_3_s50
  · exact source_gram_20_7_5_s50
  · exact source_gram_20_7_7_s50
  · exact source_gram_20_7_9_s50
  · exact source_gram_20_7_11_s50
  · exact source_gram_20_7_13_s50
  · exact source_gram_20_7_15_s50
  · exact source_gram_20_7_17_s50
  · exact source_gram_20_7_19_s50
  · exact source_gram_20_9_1_s50
  · exact source_gram_20_9_3_s50
  · exact source_gram_20_9_5_s50
  · exact source_gram_20_9_7_s50
  · exact source_gram_20_9_9_s50
  · exact source_gram_20_9_11_s50
  · exact source_gram_20_9_13_s50
  · exact source_gram_20_9_15_s50
  · exact source_gram_20_9_17_s50
  · exact source_gram_20_9_19_s50
  · exact source_gram_20_11_1_s50
  · exact source_gram_20_11_3_s50
  · exact source_gram_20_11_5_s50
  · exact source_gram_20_11_7_s50
  · exact source_gram_20_11_9_s50
  · exact source_gram_20_11_11_s50
  · exact source_gram_20_11_13_s50
  · exact source_gram_20_11_15_s50
  · exact source_gram_20_11_17_s50
  · exact source_gram_20_11_19_s50
  · exact source_gram_20_13_1_s50
  · exact source_gram_20_13_3_s50
  · exact source_gram_20_13_5_s50
  · exact source_gram_20_13_7_s50
  · exact source_gram_20_13_9_s50
  · exact source_gram_20_13_11_s50
  · exact source_gram_20_13_13_s50
  · exact source_gram_20_13_15_s50
  · exact source_gram_20_13_17_s50
  · exact source_gram_20_13_19_s50
  · exact source_gram_20_15_1_s50
  · exact source_gram_20_15_3_s50
  · exact source_gram_20_15_5_s50
  · exact source_gram_20_15_7_s50
  · exact source_gram_20_15_9_s50
  · exact source_gram_20_15_11_s50
  · exact source_gram_20_15_13_s50
  · exact source_gram_20_15_15_s50
  · exact source_gram_20_15_17_s50
  · exact source_gram_20_15_19_s50
  · exact source_gram_20_17_1_s50
  · exact source_gram_20_17_3_s50
  · exact source_gram_20_17_5_s50
  · exact source_gram_20_17_7_s50
  · exact source_gram_20_17_9_s50
  · exact source_gram_20_17_11_s50
  · exact source_gram_20_17_13_s50
  · exact source_gram_20_17_15_s50
  · exact source_gram_20_17_17_s50
  · exact source_gram_20_17_19_s50
  · exact source_gram_20_19_1_s50
  · exact source_gram_20_19_3_s50
  · exact source_gram_20_19_5_s50
  · exact source_gram_20_19_7_s50
  · exact source_gram_20_19_9_s50
  · exact source_gram_20_19_11_s50
  · exact source_gram_20_19_13_s50
  · exact source_gram_20_19_15_s50
  · exact source_gram_20_19_17_s50
  · exact source_gram_20_19_19_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_20_s50_oai := @OAI.Laughlin.Certificate.gram_20_s50_oai
