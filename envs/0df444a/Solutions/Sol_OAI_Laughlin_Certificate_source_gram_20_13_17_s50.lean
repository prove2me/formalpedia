-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_20_13_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T08:51:51.1183+00:00
-- url     : https://prove2.me/submissions/984aed0c-0516-4d8f-a7ad-05191cb357c3

import Mathlib
import Definitions.Def_OAIQ050L000

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram13Batch20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeGram_20_13_17 : GramCompute.ZFast 20 13 17 = (-108373513248000 : ℚ) := by
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

theorem source_gram_20_13_17_s50_oai : Z 20 13 17 = (-108373513248000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_20_13_17

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_20_13_17_s50_oai := @OAI.Laughlin.Certificate.source_gram_20_13_17_s50_oai
