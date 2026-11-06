-- Prove2me | solution 1 for OAI.SharpPlanar.numerical_moment_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:09:45.728671+00:00
-- url     : https://prove2.me/submissions/d9d30f6a-93a1-46bc-a43d-c1d7470fa72c

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open Complex

lemma numerical_moment_bound_e_oai : (5000:ℝ)*Real.exp 111 < (10:ℝ)^53 := by
  have he : Real.exp 1 < 11/4 := by linarith [Real.exp_one_lt_d9]
  have hex : Real.exp 111 = (Real.exp 1)^111 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hex]
  have hp : (Real.exp 1)^111 ≤ (11/4:ℝ)^111 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he.le 111
  calc
    _ ≤ 5000*(11/4:ℝ)^111 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ < _ := by norm_num

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.numerical_moment_bound_e_oai := @OAI.SharpPlanar.numerical_moment_bound_e_oai
