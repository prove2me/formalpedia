-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.contains_squareIter_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T01:04:32.035177+00:00
-- url     : https://prove2.me/submissions/1dec8b45-0b88-4700-9b39-f5252c545cea

import Mathlib
import Definitions.Def_OAIQ098G074
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g

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

namespace SharpPlanar.IntegerIntervals

lemma CBox.contains_squareIter_g_oai {a : CBox} {z : ℂ} (hz : a.Contains z) (k : ℕ) :
    (a.squareIter k).Contains (z^(2^k)) := by
  induction k with
  | zero => simpa [CBox.squareIter] using hz
  | succ k ih =>
    rw [pow_succ,show 2^k*2=2^k+2^k from by omega,pow_add]
    exact CBox.contains_mul_g ih ih

end SharpPlanar.IntegerIntervals

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.contains_squareIter_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.contains_squareIter_g_oai
