-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.exp_from_horner_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:10:11.210205+00:00
-- url     : https://prove2.me/submissions/72ecf2ca-7f43-4bb6-8750-0c4d53d259ec

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_norm_le_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_widen_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_exp_small_error_g

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

lemma exp_from_horner_g_oai {a b c : CBox} {z : ℂ} (hz : a.Contains z)
    (hn : a.NormCheck 1) (hb : b.Contains (expHorner z 0 32))
    (hc : b.WidenCheck c 1) : c.Contains (Complex.exp z) := by
  apply CBox.widen_contains_g hb _ hc
  simpa using exp_small_error_g (by simpa using CBox.norm_le_g hz hn)

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.exp_from_horner_g_oai := @OAI.SharpPlanar.IntegerIntervals.exp_from_horner_g_oai
