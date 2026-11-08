-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:42:28.783799+00:00
-- url     : https://prove2.me/submissions/9a0bbdc4-0d83-4b79-a50c-dc5301e28bba

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_rat_contains_g

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

lemma CBox.rat_contains_g_oai {a : CBox} {mr nr mi ni : ℤ} (h : a.RatCheck mr nr mi ni) :
    a.Contains ((mr:ℂ)/nr + (mi:ℂ)/ni*Complex.I) := by
  constructor
  · simpa using RBox.rat_contains_g h.1
  · simpa using RBox.rat_contains_g h.2

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.rat_contains_g_oai
