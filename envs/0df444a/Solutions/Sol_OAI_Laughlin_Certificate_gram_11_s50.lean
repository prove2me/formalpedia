-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_11_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:07:43.899794+00:00
-- url     : https://prove2.me/submissions/c4a8c1a9-d0b6-4429-87b6-e74d9dae0db7

import Mathlib
import Definitions.Def_OAIQ050L010

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_11 : GramCompute.quadruples 11 = [(0,1,2,9), (0,1,3,8), (0,1,4,7), (0,1,5,6), (0,2,3,7), (0,2,4,6), (0,3,4,5), (1,2,3,6), (1,2,4,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_11_1_1 : GramCompute.ZFast 11 1 1 = (7257600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_1_3 : GramCompute.ZFast 11 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_1_5 : GramCompute.ZFast 11 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_1_7 : GramCompute.ZFast 11 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_1_9 : GramCompute.ZFast 11 1 9 = (-453600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_1_11 : GramCompute.ZFast 11 1 11 = (9979200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_3_3 : GramCompute.ZFast 11 3 3 = (241920 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_3_5 : GramCompute.ZFast 11 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_3_7 : GramCompute.ZFast 11 3 7 = (-60480 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_3_9 : GramCompute.ZFast 11 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_3_11 : GramCompute.ZFast 11 3 11 = (2494800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_5_5 : GramCompute.ZFast 11 5 5 = (54000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_5_7 : GramCompute.ZFast 11 5 7 = (-75600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_5_9 : GramCompute.ZFast 11 5 9 = (113400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_5_11 : GramCompute.ZFast 11 5 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_7_7 : GramCompute.ZFast 11 7 7 = (120960 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_7_9 : GramCompute.ZFast 11 7 9 = (-158760 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_7_11 : GramCompute.ZFast 11 7 11 = (-623700 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_9_9 : GramCompute.ZFast 11 9 9 = (266490 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_9_11 : GramCompute.ZFast 11 9 11 = (-623700 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_11_11 : GramCompute.ZFast 11 11 11 = (39449025 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_11_1_1 : Z 11 1 1 = (7257600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_1

theorem source_gram_11_1_3 : Z 11 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_3

theorem source_gram_11_1_5 : Z 11 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_5

theorem source_gram_11_1_7 : Z 11 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_7

theorem source_gram_11_1_9 : Z 11 1 9 = (-453600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_9

theorem source_gram_11_1_11 : Z 11 1 11 = (9979200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_11

theorem source_gram_11_3_3 : Z 11 3 3 = (241920 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_3

theorem source_gram_11_3_5 : Z 11 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_5

theorem source_gram_11_3_7 : Z 11 3 7 = (-60480 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_7

theorem source_gram_11_3_9 : Z 11 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_9

theorem source_gram_11_3_11 : Z 11 3 11 = (2494800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_11

theorem source_gram_11_5_5 : Z 11 5 5 = (54000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_5

theorem source_gram_11_5_7 : Z 11 5 7 = (-75600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_7

theorem source_gram_11_5_9 : Z 11 5 9 = (113400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_9

theorem source_gram_11_5_11 : Z 11 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_11

theorem source_gram_11_7_7 : Z 11 7 7 = (120960 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_7

theorem source_gram_11_7_9 : Z 11 7 9 = (-158760 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_9

theorem source_gram_11_7_11 : Z 11 7 11 = (-623700 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_11

theorem source_gram_11_9_9 : Z 11 9 9 = (266490 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_9_9

theorem source_gram_11_9_11 : Z 11 9 11 = (-623700 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_9_11

theorem source_gram_11_11_11 : Z 11 11 11 = (39449025 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_11_11

theorem source_gram_11_3_1 : Z 11 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_3

theorem source_gram_11_5_1 : Z 11 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_5

theorem source_gram_11_5_3 : Z 11 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_5

theorem source_gram_11_7_1 : Z 11 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_7

theorem source_gram_11_7_3 : Z 11 7 3 = (-60480 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_7

theorem source_gram_11_7_5 : Z 11 7 5 = (-75600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_7

theorem source_gram_11_9_1 : Z 11 9 1 = (-453600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_9

theorem source_gram_11_9_3 : Z 11 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_9

theorem source_gram_11_9_5 : Z 11 9 5 = (113400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_9

theorem source_gram_11_9_7 : Z 11 9 7 = (-158760 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_7_9

theorem source_gram_11_11_1 : Z 11 11 1 = (9979200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_11

theorem source_gram_11_11_3 : Z 11 11 3 = (2494800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_11

theorem source_gram_11_11_5 : Z 11 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_11

theorem source_gram_11_11_7 : Z 11 11 7 = (-623700 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_7_11

theorem source_gram_11_11_9 : Z 11 11 9 = (-623700 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_9_11

theorem gram_11_s50_oai : gramRational 11 = candidateZ_11 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_11_1_1
  · exact source_gram_11_1_3
  · exact source_gram_11_1_5
  · exact source_gram_11_1_7
  · exact source_gram_11_1_9
  · exact source_gram_11_1_11
  · exact source_gram_11_3_1
  · exact source_gram_11_3_3
  · exact source_gram_11_3_5
  · exact source_gram_11_3_7
  · exact source_gram_11_3_9
  · exact source_gram_11_3_11
  · exact source_gram_11_5_1
  · exact source_gram_11_5_3
  · exact source_gram_11_5_5
  · exact source_gram_11_5_7
  · exact source_gram_11_5_9
  · exact source_gram_11_5_11
  · exact source_gram_11_7_1
  · exact source_gram_11_7_3
  · exact source_gram_11_7_5
  · exact source_gram_11_7_7
  · exact source_gram_11_7_9
  · exact source_gram_11_7_11
  · exact source_gram_11_9_1
  · exact source_gram_11_9_3
  · exact source_gram_11_9_5
  · exact source_gram_11_9_7
  · exact source_gram_11_9_9
  · exact source_gram_11_9_11
  · exact source_gram_11_11_1
  · exact source_gram_11_11_3
  · exact source_gram_11_11_5
  · exact source_gram_11_11_7
  · exact source_gram_11_11_9
  · exact source_gram_11_11_11

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_11_s50_oai := @OAI.Laughlin.Certificate.gram_11_s50_oai
