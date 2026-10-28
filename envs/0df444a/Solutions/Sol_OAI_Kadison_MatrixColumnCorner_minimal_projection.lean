-- Prove2me | solution 1 for OAI.Kadison.MatrixColumnCorner.minimal_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:06:37.242981+00:00
-- url     : https://prove2.me/submissions/7af40dfd-48ef-4df8-b5fb-f8a2a810f227

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
lemma minimal_projection_oai (i : I) : IsStarProjection (Matrix.single i i (1:ℂ)) := by
  constructor <;> simp [IsIdempotentElem,IsSelfAdjoint,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_single]

end Kadison.MatrixColumnCorner

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.MatrixColumnCorner.minimal_projection_oai.{u_1} := @OAI.Kadison.MatrixColumnCorner.minimal_projection_oai.{u_1}
