-- Prove2me | solution 1 for OAI.SharpPlanar.RBox.contains_of_abs_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:57:36.719538+00:00
-- url     : https://prove2.me/submissions/90d02154-9eaf-40f0-b4b7-cdddf43c2d3c

import Mathlib
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

lemma precision_pos : (0:ℝ) < precision := by norm_num [precision]

end IntegerIntervals
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoarseTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma RBox.contains_of_abs_e_oai {box : RBox} {x B : ℝ} (hx : |x|≤B)
    (hl : (box.lo:ℝ)≤ -B*precision) (hu : B*precision≤(box.hi:ℝ)) : box.Contains x := by
  have hp : (0:ℝ)≤precision := (by exact_mod_cast (le_of_lt precision_pos))
  have hh:=abs_le.mp hx
  simpa only [RBox.Contains,mul_comm (precision:ℝ)] using (And.intro (hl.trans (mul_le_mul_of_nonneg_right hh.1 hp)) ((mul_le_mul_of_nonneg_right hh.2 hp).trans hu))
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.RBox.contains_of_abs_e_oai := @OAI.SharpPlanar.RBox.contains_of_abs_e_oai
