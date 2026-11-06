-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_add_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:19:13.498189+00:00
-- url     : https://prove2.me/submissions/71ce1ae5-4f04-421c-8ad8-4085eb54df6c

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_add_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_add_contains_e

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

lemma CBox.contains_add_e_oai {a b : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := CBox.add_contains_e hx hy (CBox.add_check_e _ _)

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_add_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_add_e_oai
