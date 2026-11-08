-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:42:34.463983+00:00
-- url     : https://prove2.me/submissions/df0a7747-4319-4fae-9ec9-3f91a7903320

import Mathlib
import Definitions.Def_OAIQ098G083

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

lemma RBox.rat_contains_g_oai {a : RBox} {m n : ℤ} (h : a.RatCheck m n) :
    a.Contains ((m:ℝ)/n) := by
  have hn : (0:ℝ) < n := by exact_mod_cast h.1
  have h₁ : (a.lo:ℝ)*n ≤ precision*m := by exact_mod_cast h.2.1
  have h₂ : (precision:ℝ)*m ≤ a.hi*n := by exact_mod_cast h.2.2
  constructor
  · rw [← mul_div_assoc]; exact (le_div_iff₀ hn).mpr h₁
  · rw [← mul_div_assoc]; exact (div_le_iff₀ hn).mpr h₂

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains_g_oai
