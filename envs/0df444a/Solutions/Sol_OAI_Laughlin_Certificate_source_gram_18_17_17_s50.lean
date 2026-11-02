-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_18_17_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T07:41:29.691424+00:00
-- url     : https://prove2.me/submissions/372e9ccc-8555-4de7-a084-2a5f20b5ff24

import Mathlib
import Definitions.Def_OAIQ050L000

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_18 : GramCompute.quadruples 18 = [(0,1,2,16), (0,1,3,15), (0,1,4,14), (0,1,5,13), (0,1,6,12), (0,1,7,11), (0,1,8,10), (0,2,3,14), (0,2,4,13), (0,2,5,12), (0,2,6,11), (0,2,7,10), (0,2,8,9), (0,3,4,12), (0,3,5,11), (0,3,6,10), (0,3,7,9), (0,4,5,10), (0,4,6,9), (0,4,7,8), (0,5,6,8), (1,2,3,13), (1,2,4,12), (1,2,5,11), (1,2,6,10), (1,2,7,9), (1,3,4,11), (1,3,5,10), (1,3,6,9), (1,3,7,8), (1,4,5,9), (1,4,6,8), (1,5,6,7), (2,3,4,10), (2,3,5,9), (2,3,6,8), (2,4,5,8), (2,4,6,7), (3,4,5,7)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram171718
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_17_17 : GramCompute.ZFast 18 17 17 = (354298024080000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_18_17_17_s50_oai : Z 18 17 17 = (354298024080000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_17_17

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_18_17_17_s50_oai := @OAI.Laughlin.Certificate.source_gram_18_17_17_s50_oai
