-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.ofReal_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:09:53.02825+00:00
-- url     : https://prove2.me/submissions/4a41e43b-38f7-4a08-bc0d-c56938e409e0

import Mathlib
import Definitions.Def_OAIQ098G083

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

namespace SharpPlanar
namespace IntegerIntervals

lemma CBox.ofReal_contains_g_oai {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (⟨a,⟨0,0⟩⟩ : CBox).Contains (x:ℂ) := by
  exact ⟨hx,by simp [RBox.Contains]⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.ofReal_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.ofReal_contains_g_oai
