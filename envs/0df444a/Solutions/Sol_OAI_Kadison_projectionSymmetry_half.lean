-- Prove2me | solution 1 for OAI.Kadison.projectionSymmetry_half
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:09:05.977699+00:00
-- url     : https://prove2.me/submissions/e120c01b-a2ed-4ed5-9c33-e2c1b8ffe982

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

lemma projectionSymmetry_half_oai : p=(1/2:ℂ) • (1+(projectionSymmetry hp:A)) := by
  rw [projectionSymmetry_coe,show (1:A)+(p+p-1)=p+p by abel,←two_smul ℂ p,smul_smul]
  norm_num

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.projectionSymmetry_half_oai.{u_1} := @OAI.Kadison.projectionSymmetry_half_oai.{u_1}
