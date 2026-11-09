-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.add_check_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:32:45.046238+00:00
-- url     : https://prove2.me/submissions/d69592cb-01b1-4792-bc9f-cb80cb727e70

import Mathlib
import Definitions.Def_OAIQ098G076
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_check_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

lemma CBox.add_check_g_oai (a b : CBox) : a.AddCheck b (a.add b) :=
  ⟨RBox.add_check_g _ _,RBox.add_check_g _ _⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.add_check_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.add_check_g_oai
