-- Prove2me | solution 1 for OAI.Kadison.isStarProjection_corner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:20:37.807986+00:00
-- url     : https://prove2.me/submissions/9ca7d75f-1898-4126-8969-1ed345d0f285

import Mathlib
import Definitions.Def_OAIQ039C004

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixColumnCorner
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
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

lemma isStarProjection_corner_oai {e : Corner hp} (he : IsStarProjection (e:A)) :
    IsStarProjection e := by
  constructor
  · exact Subtype.ext he.isIdempotentElem.eq
  · exact Subtype.ext he.isSelfAdjoint.star_eq

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.isStarProjection_corner_oai.{u_1} := @OAI.Kadison.isStarProjection_corner_oai.{u_1}
