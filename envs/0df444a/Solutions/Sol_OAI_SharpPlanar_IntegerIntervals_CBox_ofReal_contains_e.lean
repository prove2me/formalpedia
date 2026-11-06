-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.ofReal_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:26:35.551466+00:00
-- url     : https://prove2.me/submissions/d3cd9ca2-5c3e-4576-b312-23331367f8ad

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

namespace SharpPlanar
namespace IntegerIntervals

lemma CBox.ofReal_contains_e_oai {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (⟨a,⟨0,0⟩⟩ : CBox).Contains (x:ℂ) := by
  exact ⟨hx,by simp [RBox.Contains]⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.ofReal_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.ofReal_contains_e_oai
