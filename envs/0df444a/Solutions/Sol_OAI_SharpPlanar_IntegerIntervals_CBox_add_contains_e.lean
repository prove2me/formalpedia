-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:18:05.321027+00:00
-- url     : https://prove2.me/submissions/c1df6c8f-bc94-4e67-bd75-2a2ad09cb268

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_contains_e

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

lemma CBox.add_contains_e_oai {a b c : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.AddCheck b c) : c.Contains (x+y) :=
  ⟨RBox.add_contains_e hx.1 hy.1 hc.1,RBox.add_contains_e hx.2 hy.2 hc.2⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.add_contains_e_oai
