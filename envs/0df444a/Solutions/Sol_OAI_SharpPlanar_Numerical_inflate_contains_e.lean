-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.inflate_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:56:52.809026+00:00
-- url     : https://prove2.me/submissions/7ad1f93e-e387-42a5-b1a8-33e29796a06b

import Mathlib
import Definitions.Def_OAIQ098E028
import Definitions.Def_OAIQ098E030

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
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma inflate_contains_e_oai {a : RBox} {x y : ℝ} (hx : a.Contains x) (he : |y-x| < 1/10^22) :
    (inflate a).Contains y := by
  have he' := abs_lt.mp he
  have hp := precision_pos
  have hL := mul_lt_mul_of_pos_left he'.1 hp
  have hU := mul_lt_mul_of_pos_left he'.2 hp
  constructor <;> dsimp [inflate] <;> push_cast <;>
    norm_num [RBox.Contains,precision] at hL hU hx ⊢ <;> linarith only [hx.1,hx.2,hL,hU]

end Numerical
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.inflate_contains_e_oai := @OAI.SharpPlanar.Numerical.inflate_contains_e_oai
