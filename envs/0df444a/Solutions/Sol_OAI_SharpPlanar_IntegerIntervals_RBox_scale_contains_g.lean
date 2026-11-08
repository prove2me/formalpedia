-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.scale_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:47:05.061918+00:00
-- url     : https://prove2.me/submissions/41878ed3-9aaa-4c29-872f-86ecc4f87f3e

import Mathlib
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_between_mul_g

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

lemma RBox.scale_contains_g_oai {a c : RBox} {x : ℝ} {m n : ℤ} (hx : a.Contains x)
    (hc : a.ScaleCheck c m n) : c.Contains (((m:ℝ)/n)*x) := by
  have hn : (0:ℝ) < n := by exact_mod_cast hc.1
  have h₁ : (c.lo:ℝ)*n ≤ min ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) := by exact_mod_cast hc.2.1
  have h₂ : max ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) ≤ (c.hi:ℝ)*n := by exact_mod_cast hc.2.2
  have hh : min ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) ≤ (m:ℝ)*(precision*x) ∧
      (m:ℝ)*(precision*x) ≤ max ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) := by
    apply between_mul_g hx <;> simp
  constructor
  · apply (mul_le_mul_iff_right₀ hn).mp
    convert h₁.trans hh.1 using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  · apply (mul_le_mul_iff_right₀ hn).mp
    convert hh.2.trans h₂ using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.scale_contains_g_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.scale_contains_g_oai
