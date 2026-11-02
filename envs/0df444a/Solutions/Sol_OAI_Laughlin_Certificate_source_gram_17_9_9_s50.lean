-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_17_9_9_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T07:23:33.395559+00:00
-- url     : https://prove2.me/submissions/5d4fbe52-63f9-4003-b724-a313e91d6e74

import Mathlib
import Definitions.Def_OAIQ050L000

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeQuadruples17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_17 : GramCompute.quadruples 17 = [(0,1,2,15), (0,1,3,14), (0,1,4,13), (0,1,5,12), (0,1,6,11), (0,1,7,10), (0,1,8,9), (0,2,3,13), (0,2,4,12), (0,2,5,11), (0,2,6,10), (0,2,7,9), (0,3,4,11), (0,3,5,10), (0,3,6,9), (0,3,7,8), (0,4,5,9), (0,4,6,8), (0,5,6,7), (1,2,3,12), (1,2,4,11), (1,2,5,10), (1,2,6,9), (1,2,7,8), (1,3,4,10), (1,3,5,9), (1,3,6,8), (1,4,5,8), (1,4,6,7), (2,3,4,9), (2,3,5,8), (2,3,6,7), (2,4,5,7), (3,4,5,6)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeGram09Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_17_9_9 : GramCompute.ZFast 17 9 9 = (5372438400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_17_9_9_s50_oai : Z 17 9 9 = (5372438400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_9_9

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_17_9_9_s50_oai := @OAI.Laughlin.Certificate.source_gram_17_9_9_s50_oai
