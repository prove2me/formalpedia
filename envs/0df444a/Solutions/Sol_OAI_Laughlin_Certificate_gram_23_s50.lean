-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_23_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:18:36.084835+00:00
-- url     : https://prove2.me/submissions/aee31164-a33f-4903-bcd8-7ce6870d724a

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_11_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_13_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_15_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_17_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_19_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_21_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_23_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_3_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_3_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_23_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples23
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram01Batch23
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram03Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

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

theorem computeGram_23_3_21 : GramCompute.ZFast 23 3 21 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram05Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeGram_23_5_7 : GramCompute.ZFast 23 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData23
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

theorem source_gram_23_3_21 : Z 23 3 21 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_3_21

theorem source_gram_23_5_7 : Z 23 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_7

theorem gram_23_s50_oai : gramRational 23 = candidateZ_23 := by
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
  · exact source_gram_23_3_1_s50
  · exact source_gram_23_3_3_s50
  · exact source_gram_23_3_5
  · exact source_gram_23_3_7
  · exact source_gram_23_3_9
  · exact source_gram_23_3_11
  · exact source_gram_23_3_13
  · exact source_gram_23_3_15
  · exact source_gram_23_3_17
  · exact source_gram_23_3_19_s50
  · exact source_gram_23_3_21
  · exact source_gram_23_3_23_s50
  · exact source_gram_23_5_1_s50
  · exact source_gram_23_5_3_s50
  · exact source_gram_23_5_5_s50
  · exact source_gram_23_5_7
  · exact source_gram_23_5_9_s50
  · exact source_gram_23_5_11_s50
  · exact source_gram_23_5_13_s50
  · exact source_gram_23_5_15_s50
  · exact source_gram_23_5_17_s50
  · exact source_gram_23_5_19_s50
  · exact source_gram_23_5_21_s50
  · exact source_gram_23_5_23_s50
  · exact source_gram_23_7_1_s50
  · exact source_gram_23_7_3_s50
  · exact source_gram_23_7_5_s50
  · exact source_gram_23_7_7_s50
  · exact source_gram_23_7_9_s50
  · exact source_gram_23_7_11_s50
  · exact source_gram_23_7_13_s50
  · exact source_gram_23_7_15_s50
  · exact source_gram_23_7_17_s50
  · exact source_gram_23_7_19_s50
  · exact source_gram_23_7_21_s50
  · exact source_gram_23_7_23_s50
  · exact source_gram_23_9_1_s50
  · exact source_gram_23_9_3_s50
  · exact source_gram_23_9_5_s50
  · exact source_gram_23_9_7_s50
  · exact source_gram_23_9_9_s50
  · exact source_gram_23_9_11_s50
  · exact source_gram_23_9_13_s50
  · exact source_gram_23_9_15_s50
  · exact source_gram_23_9_17_s50
  · exact source_gram_23_9_19_s50
  · exact source_gram_23_9_21_s50
  · exact source_gram_23_9_23_s50
  · exact source_gram_23_11_1_s50
  · exact source_gram_23_11_3_s50
  · exact source_gram_23_11_5_s50
  · exact source_gram_23_11_7_s50
  · exact source_gram_23_11_9_s50
  · exact source_gram_23_11_11_s50
  · exact source_gram_23_11_13_s50
  · exact source_gram_23_11_15_s50
  · exact source_gram_23_11_17_s50
  · exact source_gram_23_11_19_s50
  · exact source_gram_23_11_21_s50
  · exact source_gram_23_11_23_s50
  · exact source_gram_23_13_1_s50
  · exact source_gram_23_13_3_s50
  · exact source_gram_23_13_5_s50
  · exact source_gram_23_13_7_s50
  · exact source_gram_23_13_9_s50
  · exact source_gram_23_13_11_s50
  · exact source_gram_23_13_13_s50
  · exact source_gram_23_13_15_s50
  · exact source_gram_23_13_17_s50
  · exact source_gram_23_13_19_s50
  · exact source_gram_23_13_21_s50
  · exact source_gram_23_13_23_s50
  · exact source_gram_23_15_1_s50
  · exact source_gram_23_15_3_s50
  · exact source_gram_23_15_5_s50
  · exact source_gram_23_15_7_s50
  · exact source_gram_23_15_9_s50
  · exact source_gram_23_15_11_s50
  · exact source_gram_23_15_13_s50
  · exact source_gram_23_15_15_s50
  · exact source_gram_23_15_17_s50
  · exact source_gram_23_15_19_s50
  · exact source_gram_23_15_21_s50
  · exact source_gram_23_15_23_s50
  · exact source_gram_23_17_1_s50
  · exact source_gram_23_17_3_s50
  · exact source_gram_23_17_5_s50
  · exact source_gram_23_17_7_s50
  · exact source_gram_23_17_9_s50
  · exact source_gram_23_17_11_s50
  · exact source_gram_23_17_13_s50
  · exact source_gram_23_17_15_s50
  · exact source_gram_23_17_17_s50
  · exact source_gram_23_17_19_s50
  · exact source_gram_23_17_21_s50
  · exact source_gram_23_17_23_s50
  · exact source_gram_23_19_1_s50
  · exact source_gram_23_19_3_s50
  · exact source_gram_23_19_5_s50
  · exact source_gram_23_19_7_s50
  · exact source_gram_23_19_9_s50
  · exact source_gram_23_19_11_s50
  · exact source_gram_23_19_13_s50
  · exact source_gram_23_19_15_s50
  · exact source_gram_23_19_17_s50
  · exact source_gram_23_19_19_s50
  · exact source_gram_23_19_21_s50
  · exact source_gram_23_19_23_s50
  · exact source_gram_23_21_1_s50
  · exact source_gram_23_21_3_s50
  · exact source_gram_23_21_5_s50
  · exact source_gram_23_21_7_s50
  · exact source_gram_23_21_9_s50
  · exact source_gram_23_21_11_s50
  · exact source_gram_23_21_13_s50
  · exact source_gram_23_21_15_s50
  · exact source_gram_23_21_17_s50
  · exact source_gram_23_21_19_s50
  · exact source_gram_23_21_21_s50
  · exact source_gram_23_21_23_s50
  · exact source_gram_23_23_1_s50
  · exact source_gram_23_23_3_s50
  · exact source_gram_23_23_5_s50
  · exact source_gram_23_23_7_s50
  · exact source_gram_23_23_9_s50
  · exact source_gram_23_23_11_s50
  · exact source_gram_23_23_13_s50
  · exact source_gram_23_23_15_s50
  · exact source_gram_23_23_17_s50
  · exact source_gram_23_23_19_s50
  · exact source_gram_23_23_21_s50
  · exact source_gram_23_23_23_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_23_s50_oai := @OAI.Laughlin.Certificate.gram_23_s50_oai
