-- Prove2me | solution 1 for OAI.SharpPlanar.approximate_inverse_bijective_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:04:26.329855+00:00
-- url     : https://prove2.me/submissions/f3e1b589-bf82-46b5-91ad-9caec462701c

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma approximate_inverse_bijective_e_oai (A W : E →L[ℝ] E) (h : ‖1-W*A‖ < 1) :
    Function.Bijective A := by
  have hu : IsUnit (W*A) := by
    convert isUnit_one_sub_of_norm_lt_one h using 1
    all_goals try with_reducible_and_instances rfl
    abel
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).injective
  have hai : Function.Injective A := by
    intro x y hxy
    apply hi
    change W (A x) = W (A y)
    rw [hxy]
  exact ⟨hai,LinearMap.injective_iff_surjective.mp hai⟩

end Inverse
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.approximate_inverse_bijective_e_oai.{u_1} := @OAI.SharpPlanar.approximate_inverse_bijective_e_oai.{u_1}
