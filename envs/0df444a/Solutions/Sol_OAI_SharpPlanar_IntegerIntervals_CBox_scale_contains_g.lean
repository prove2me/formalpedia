-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.scale_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:46:48.677347+00:00
-- url     : https://prove2.me/submissions/63c0bf3b-198d-427e-8006-c551ef02acfc

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_scale_contains_g

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

lemma CBox.scale_contains_g_oai {a c : CBox} {z : ℂ} {m n : ℤ} (hz : a.Contains z)
    (hc : a.ScaleCheck c m n) : c.Contains (((m:ℂ)/n)*z) := by
  constructor
  · simpa using RBox.scale_contains_g hz.1 hc.1
  · simpa using RBox.scale_contains_g hz.2 hc.2

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.scale_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.scale_contains_g_oai
