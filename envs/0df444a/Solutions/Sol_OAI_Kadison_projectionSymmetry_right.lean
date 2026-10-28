-- Prove2me | solution 1 for OAI.Kadison.projectionSymmetry_right
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:10:13.867981+00:00
-- url     : https://prove2.me/submissions/37d7cbc2-0db1-4379-8a63-af7ae3020108

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

lemma projectionSymmetry_right_oai : (projectionSymmetry hp:A)*p=p := by
  rw [projectionSymmetry_coe,sub_mul,add_mul,hp.isIdempotentElem.eq,one_mul]
  abel

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.projectionSymmetry_right_oai.{u_1} := @OAI.Kadison.projectionSymmetry_right_oai.{u_1}
