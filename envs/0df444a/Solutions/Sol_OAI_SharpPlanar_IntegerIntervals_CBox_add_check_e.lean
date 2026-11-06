-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.add_check_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:17:19.468544+00:00
-- url     : https://prove2.me/submissions/d87d0db9-bfea-49d4-90c1-441ee5291951

import Mathlib
import Definitions.Def_OAIQ098E031

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

lemma RBox.add_check (a b : RBox) : a.AddCheck b (a.add b) := ⟨le_rfl,le_rfl⟩
lemma CBox.add_check_e_oai (a b : CBox) : a.AddCheck b (a.add b) :=
  ⟨RBox.add_check _ _,RBox.add_check _ _⟩

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.add_check_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.add_check_e_oai
