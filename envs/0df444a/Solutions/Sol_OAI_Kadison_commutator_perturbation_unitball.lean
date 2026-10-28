-- Prove2me | solution 1 for OAI.Kadison.commutator_perturbation_unitball
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:09:22.487898+00:00
-- url     : https://prove2.me/submissions/4abbc4ee-87ef-45bb-81b8-38c2c52dff9a

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_MainCommutantDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma operator_commutator_norm_le (Y Z : K →L[ℂ] K) : ‖Y*Z-Z*Y‖≤2*‖Y‖*‖Z‖ := by
  calc
    _ ≤ ‖Y*Z‖+‖Z*Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖*‖Z‖+‖Z‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSquareConditionalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma commutator_perturbation_unitball_oai (Y Z A : K →L[ℂ] K) {b e : ℝ}
    (hb : ‖Z*A-A*Z‖ ≤ b) (he : ‖Y-Z‖ ≤ e) (hA : ‖A‖ ≤ 1) :
    ‖Y*A-A*Y‖ ≤ b+2*e := by
  have hid : Y*A-A*Y=(Z*A-A*Z)+((Y-Z)*A-A*(Y-Z)) := by
    simp only [sub_mul,mul_sub]; abel
  rw [hid]
  have hn : 0 ≤ e := (norm_nonneg _).trans he
  calc
    _ ≤ ‖Z*A-A*Z‖+‖(Y-Z)*A-A*(Y-Z)‖ := norm_add_le _ _
    _ ≤ b+2*‖Y-Z‖*‖A‖ := add_le_add hb (operator_commutator_norm_le _ _)
    _ ≤ b+2*e := by nlinarith [norm_nonneg (Y-Z),norm_nonneg A]

end Kadison

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.commutator_perturbation_unitball_oai.{u_1} := @OAI.Kadison.commutator_perturbation_unitball_oai.{u_1}
