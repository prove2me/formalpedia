-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.RBox.abs_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:50:14.973086+00:00
-- url     : https://prove2.me/submissions/751ab59d-9ab7-4c8d-b957-7ced5a3948ad

import Mathlib
import Definitions.Def_OAIQ098E019
import Definitions.Def_OAIQ098E028

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

lemma precision_pos : (0:ℝ) < precision := by norm_num [precision]

lemma RBox.abs_bound_e_oai {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (precision:ℝ)*|x| ≤ (a.bound:ℝ) := by
  rw [← abs_of_pos precision_pos,← abs_mul,abs_le]
  have h₁ : -(a.bound:ℝ) ≤ (a.lo:ℝ) := by
    have hh := (neg_abs_le a.lo).trans (le_refl a.lo)
    have hu : |a.lo| ≤ a.bound := le_max_left _ _
    exact_mod_cast (neg_le_neg hu).trans hh
  have h₂ : (a.hi:ℝ) ≤ (a.bound:ℝ) := by
    exact_mod_cast (le_abs_self a.hi).trans (le_max_right |a.lo| |a.hi|)
  exact ⟨h₁.trans hx.1,hx.2.trans h₂⟩

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.RBox.abs_bound_e_oai := @OAI.SharpPlanar.IntegerIntervals.RBox.abs_bound_e_oai
