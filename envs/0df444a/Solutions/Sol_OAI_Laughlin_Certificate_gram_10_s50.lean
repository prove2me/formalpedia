-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_10_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:06:07.928785+00:00
-- url     : https://prove2.me/submissions/77cde668-a3b2-4021-b42f-66e925eb033c

import Mathlib
import Definitions.Def_OAIQ050L010

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_10 : GramCompute.quadruples 10 = [(0,1,2,8), (0,1,3,7), (0,1,4,6), (0,2,3,6), (0,2,4,5), (1,2,3,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_10_1_1 : GramCompute.ZFast 10 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_1_3 : GramCompute.ZFast 10 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_1_5 : GramCompute.ZFast 10 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_1_7 : GramCompute.ZFast 10 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_1_9 : GramCompute.ZFast 10 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_3_3 : GramCompute.ZFast 10 3 3 = (30240 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_3_5 : GramCompute.ZFast 10 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_3_7 : GramCompute.ZFast 10 3 7 = (-22680 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_3_9 : GramCompute.ZFast 10 3 9 = (90720 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_5_5 : GramCompute.ZFast 10 5 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_5_7 : GramCompute.ZFast 10 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_5_9 : GramCompute.ZFast 10 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_7_7 : GramCompute.ZFast 10 7 7 = (17010 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_7_9 : GramCompute.ZFast 10 7 9 = (-68040 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_9_9 : GramCompute.ZFast 10 9 9 = (272160 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Symmetry
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_10_1_1 : Z 10 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_1

theorem source_gram_10_1_3 : Z 10 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_3

theorem source_gram_10_1_5 : Z 10 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_5

theorem source_gram_10_1_7 : Z 10 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_7

theorem source_gram_10_1_9 : Z 10 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_9

theorem source_gram_10_3_3 : Z 10 3 3 = (30240 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_3

theorem source_gram_10_3_5 : Z 10 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_5

theorem source_gram_10_3_7 : Z 10 3 7 = (-22680 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_7

theorem source_gram_10_3_9 : Z 10 3 9 = (90720 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_9

theorem source_gram_10_5_5 : Z 10 5 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_5

theorem source_gram_10_5_7 : Z 10 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_7

theorem source_gram_10_5_9 : Z 10 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_9

theorem source_gram_10_7_7 : Z 10 7 7 = (17010 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_7_7

theorem source_gram_10_7_9 : Z 10 7 9 = (-68040 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_7_9

theorem source_gram_10_9_9 : Z 10 9 9 = (272160 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_9_9

theorem source_gram_10_3_1 : Z 10 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_3

theorem source_gram_10_5_1 : Z 10 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_5

theorem source_gram_10_5_3 : Z 10 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_5

theorem source_gram_10_7_1 : Z 10 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_7

theorem source_gram_10_7_3 : Z 10 7 3 = (-22680 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_7

theorem source_gram_10_7_5 : Z 10 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_5_7

theorem source_gram_10_9_1 : Z 10 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_9

theorem source_gram_10_9_3 : Z 10 9 3 = (90720 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_9

theorem source_gram_10_9_5 : Z 10 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_5_9

theorem source_gram_10_9_7 : Z 10 9 7 = (-68040 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_7_9

theorem gram_10_s50_oai : gramRational 10 = candidateZ_10 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_10_1_1
  · exact source_gram_10_1_3
  · exact source_gram_10_1_5
  · exact source_gram_10_1_7
  · exact source_gram_10_1_9
  · exact source_gram_10_3_1
  · exact source_gram_10_3_3
  · exact source_gram_10_3_5
  · exact source_gram_10_3_7
  · exact source_gram_10_3_9
  · exact source_gram_10_5_1
  · exact source_gram_10_5_3
  · exact source_gram_10_5_5
  · exact source_gram_10_5_7
  · exact source_gram_10_5_9
  · exact source_gram_10_7_1
  · exact source_gram_10_7_3
  · exact source_gram_10_7_5
  · exact source_gram_10_7_7
  · exact source_gram_10_7_9
  · exact source_gram_10_9_1
  · exact source_gram_10_9_3
  · exact source_gram_10_9_5
  · exact source_gram_10_9_7
  · exact source_gram_10_9_9

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_10_s50_oai := @OAI.Laughlin.Certificate.gram_10_s50_oai
