-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_13_7_1_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:32:05.457375+00:00
-- url     : https://prove2.me/submissions/a5ca17b3-63cd-4c7f-bf03-9940b2695af3

import Mathlib
import Definitions.Def_OAIQ050L000

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

theorem computeGram_13_1_7 : GramCompute.ZFast 13 1 7 = (0 : ℚ) := by
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_13_1_7 : Z 13 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_7

theorem source_gram_13_7_1_s50_oai : Z 13 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_7

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_13_7_1_s50_oai := @OAI.Laughlin.Certificate.source_gram_13_7_1_s50_oai
