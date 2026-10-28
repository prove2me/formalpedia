-- Prove2me | solution 1 for OAI.Kadison.MatrixColumnCorner.full_column
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:06:14.545659+00:00
-- url     : https://prove2.me/submissions/54d27bab-9880-429c-a3ba-208d02876941

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixColumnCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.MatrixColumnCorner

variable {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [CStarAlgebra D]

omit [Nonempty I] in
lemma full_column_oai (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) (i0 : I) :
    (∀ i j, star (φ (Matrix.single i i0 1))*φ (Matrix.single j i0 1)=
      if i=j then φ (Matrix.single i0 i0 1) else 0) ∧
    (∀ i, φ (Matrix.single i0 i0 1)*star (φ (Matrix.single i i0 1))=
      star (φ (Matrix.single i i0 1))) ∧
    ∑ i,φ (Matrix.single i i0 1)*star (φ (Matrix.single i i0 1))=1 := by
  constructor
  · intro i j
    rw [←map_star,←map_mul]
    by_cases hij : i=j
    · subst j; simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single]
    · simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single,hij]
  constructor
  · intro i
    rw [←map_star,←map_mul]
    simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single]
  · simp only [←map_star,←map_mul,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single,star_one,
      Matrix.single_mul_single_same,one_mul,←map_sum,Matrix.sum_single_one,map_one]

end Kadison.MatrixColumnCorner

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.MatrixColumnCorner.full_column_oai.{u_1, u_2} := @OAI.Kadison.MatrixColumnCorner.full_column_oai.{u_1, u_2}
