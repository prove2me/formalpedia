-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:54:16.077863+00:00
-- url     : https://prove2.me/submissions/d4867b72-114f-4557-a816-b0f7608b943a

import Mathlib
import Definitions.Def_OAIQ098E028
import Definitions.Def_OAIQ098E030

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

lemma RBox.rat_contains_e_oai {a : RBox} {m n : ℤ} (h : a.RatCheck m n) :
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

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.rat_contains_e_oai
