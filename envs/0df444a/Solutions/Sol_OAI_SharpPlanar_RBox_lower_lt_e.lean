-- Prove2me | solution 1 for OAI.SharpPlanar.RBox.lower_lt_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:58:41.768789+00:00
-- url     : https://prove2.me/submissions/c3634fae-5860-47a6-97cb-5dec2454f6e9

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
-- module Solutions.OAIQ098_PP.PlanarPacking_BernsteinBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
open scoped BigOperators
lemma RBox.lower_lt_e_oai {box : RBox} {x : ℝ} {u v : ℤ} (hh : box.Contains x)
    (hv : 0<v) (hc : precision*u<box.lo*v) : (u:ℝ)/v<x := by
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have hc' : (precision:ℝ)*u<(box.lo:ℝ)*v := by exact_mod_cast hc
  have hc'' := hc'.trans_le (mul_le_mul_of_nonneg_right hh.1 hv'.le)
  apply (div_lt_iff₀ hv').mpr
  nlinarith [precision_pos]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.RBox.lower_lt_e_oai := @OAI.SharpPlanar.RBox.lower_lt_e_oai
