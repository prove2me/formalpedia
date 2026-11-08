-- Prove2me | solution 1 for OAI.SharpPlanar.RBox.lower_lt_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:08:32.900201+00:00
-- url     : https://prove2.me/submissions/b59860b5-2b4f-40de-a466-36cc306d696d

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g

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
lemma RBox.lower_lt_g_oai {box : RBox} {x : ℝ} {u v : ℤ} (hh : box.Contains x)
    (hv : 0<v) (hc : precision*u<box.lo*v) : (u:ℝ)/v<x := by
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have hc' : (precision:ℝ)*u<(box.lo:ℝ)*v := by exact_mod_cast hc
  have hc'' := hc'.trans_le (mul_le_mul_of_nonneg_right hh.1 hv'.le)
  apply (div_lt_iff₀ hv').mpr
  nlinarith [precision_pos_g]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.RBox.lower_lt_g_oai := @OAI.SharpPlanar.RBox.lower_lt_g_oai
