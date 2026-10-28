-- Prove2me | solution 1 for OAI.Kadison.projectionSymmetry_left
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:09:28.909218+00:00
-- url     : https://prove2.me/submissions/c804f6e4-32ea-4f23-bc3b-aff150f386da

import Mathlib
import Definitions.Def_OAIQ039C019

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

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

include hp

lemma projectionSymmetry_left_oai : p*(projectionSymmetry hp:A)=p := by
  rw [projectionSymmetry_coe,mul_sub,mul_add,hp.isIdempotentElem.eq,mul_one]
  abel

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.projectionSymmetry_left_oai.{u_1} := @OAI.Kadison.projectionSymmetry_left_oai.{u_1}
