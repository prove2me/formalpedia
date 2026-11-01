-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_13_5_7_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:30:24.57391+00:00
-- url     : https://prove2.me/submissions/1487dd11-c837-4066-93a7-a46629298688

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram05Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeGram_13_5_7 : GramCompute.ZFast 13 5 7 = (-907200 : ℚ) := by
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

theorem source_gram_13_5_7_s50_oai : Z 13 5 7 = (-907200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_7

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_13_5_7_s50_oai := @OAI.Laughlin.Certificate.source_gram_13_5_7_s50_oai
