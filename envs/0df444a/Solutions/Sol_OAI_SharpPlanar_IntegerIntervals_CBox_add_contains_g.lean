-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:32:47.87174+00:00
-- url     : https://prove2.me/submissions/d89e974d-2ca8-437e-8b94-8c8e360da27a

import Mathlib
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_contains_g

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

lemma CBox.add_contains_g_oai {a b c : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.AddCheck b c) : c.Contains (x+y) :=
  ⟨RBox.add_contains_g hx.1 hy.1 hc.1,RBox.add_contains_g hx.2 hy.2 hc.2⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_g_oai
