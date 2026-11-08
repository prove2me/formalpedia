-- Prove2me | solution 1 for OAI.SharpPlanar.RBox.contains_of_abs_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:07:57.621239+00:00
-- url     : https://prove2.me/submissions/13c29e96-c36a-4762-9fd7-63832530ff64

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoarseTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma RBox.contains_of_abs_g_oai {box : RBox} {x B : ℝ} (hx : |x|≤B)
    (hl : (box.lo:ℝ)≤ -B*precision) (hu : B*precision≤(box.hi:ℝ)) : box.Contains x := by
  have hp : (0:ℝ)≤precision := (by exact_mod_cast (le_of_lt precision_pos_g))
  have hh:=abs_le.mp hx
  simpa only [RBox.Contains,mul_comm (precision:ℝ)] using (And.intro (hl.trans (mul_le_mul_of_nonneg_right hh.1 hp)) ((mul_le_mul_of_nonneg_right hh.2 hp).trans hu))
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.RBox.contains_of_abs_g_oai := @OAI.SharpPlanar.RBox.contains_of_abs_g_oai
