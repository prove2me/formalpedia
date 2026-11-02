-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_23_7_5_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:24:29.751398+00:00
-- url     : https://prove2.me/submissions/a8fdc0aa-7e66-4756-ab54-668f3cd1b502

import Mathlib
import Definitions.Def_OAIQ050L000

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_23_5_7 : Z 23 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_23_5_7

theorem source_gram_23_7_5_s50_oai : Z 23 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_23_5_7

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_23_7_5_s50_oai := @OAI.Laughlin.Certificate.source_gram_23_7_5_s50_oai
