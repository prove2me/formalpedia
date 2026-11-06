-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.add_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:50:58.522404+00:00
-- url     : https://prove2.me/submissions/854bd26a-ebb7-4388-b75b-e1652fa1e537

import Mathlib
import Definitions.Def_OAIQ098E026
import Definitions.Def_OAIQ098E028

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

lemma RBox.add_contains_e_oai {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.AddCheck b c) : c.Contains (x+y) := by
  have h₁ : (c.lo:ℝ) ≤ a.lo+b.lo := by exact_mod_cast hc.1
  have h₂ : (a.hi:ℝ)+b.hi ≤ c.hi := by exact_mod_cast hc.2
  constructor <;> nlinarith only [hx.1,hx.2,hy.1,hy.2,h₁,h₂]

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.add_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.add_contains_e_oai
