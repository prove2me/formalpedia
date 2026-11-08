-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.inflate_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:57:10.106306+00:00
-- url     : https://prove2.me/submissions/de414021-5e2e-4bea-b4a1-ce248a9c3b45

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g

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

lemma inflate_contains_g_oai {a : RBox} {x y : ℝ} (hx : a.Contains x) (he : |y-x| < 1/10^22) :
    (inflate a).Contains y := by
  have he' := abs_lt.mp he
  have hp := precision_pos_g
  have hL := mul_lt_mul_of_pos_left he'.1 hp
  have hU := mul_lt_mul_of_pos_left he'.2 hp
  constructor <;> dsimp [inflate] <;> push_cast <;>
    norm_num [RBox.Contains,precision] at hL hU hx ⊢ <;> linarith only [hx.1,hx.2,hL,hU]

end Numerical
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.inflate_contains_g_oai := @OAI.SharpPlanar.Numerical.inflate_contains_g_oai
