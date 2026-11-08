-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.CBox.neg_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:39:26.251654+00:00
-- url     : https://prove2.me/submissions/eb40819e-b2f0-40bc-911d-6bbdee8cce6e

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g

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

lemma CBox.neg_contains_g_oai {a : CBox} {z : ℂ} (hz : a.Contains z) : a.neg.Contains (-z) :=
  ⟨RBox.neg_contains_g hz.1,RBox.neg_contains_g hz.2⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.CBox.neg_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.CBox.neg_contains_g_oai
