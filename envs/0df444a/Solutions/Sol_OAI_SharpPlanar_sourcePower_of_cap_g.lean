-- Prove2me | solution 1 for OAI.SharpPlanar.sourcePower_of_cap_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T22:34:45.947644+00:00
-- url     : https://prove2.me/submissions/c619de7f-e886-40b1-9eb0-a2ea5f7535da

import Mathlib
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1690
import Theorems.Thm_OAI_SharpPlanar_sourcePower_sharp_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoarseTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma sourcePower_of_cap_g_oai (a : Bool) (n : ℕ) (y : ℝ) (nu r : ℕ) {B : ℝ}
    (hB : sharpTaylor (r+nu) n/((r+nu).factorial:ℝ)≤B) :
    |sourcePower a n y nu r| ≤ |y|^r*B := by
  exact (sourcePower_sharp_g a n y nu r).trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hB (pow_nonneg (abs_nonneg y) r))
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.sourcePower_of_cap_g_oai := @OAI.SharpPlanar.sourcePower_of_cap_g_oai
