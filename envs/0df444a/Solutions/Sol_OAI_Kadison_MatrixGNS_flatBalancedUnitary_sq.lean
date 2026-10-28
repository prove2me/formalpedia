-- Prove2me | solution 1 for OAI.Kadison.MatrixGNS.flatBalancedUnitary_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:28:17.761402+00:00
-- url     : https://prove2.me/submissions/4fa5b314-699f-4533-a9a0-f4961d9ff3c6

import Mathlib
import Definitions.Def_OAIQ039C028

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFlatten
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance instDecidableEq_solutions_1_rdc7d82_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixGNS.instDecidableEq_solutions_2
attribute [local instance] OAI.Kadison.MatrixGNS.instDecidableEqProd_solutions
lemma flatBalancedUnitary_sq_oai (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)*
      (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)=1 := by
  change flatten ι (Fin 2) (BalancedDilation.symmetry X)*
    flatten ι (Fin 2) (BalancedDilation.symmetry X)=1
  rw [←map_mul,BalancedDilation.symmetry_mul_self X hX,map_one]

end Kadison.MatrixGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.MatrixGNS.flatBalancedUnitary_sq_oai.{u_1, u_2} := @OAI.Kadison.MatrixGNS.flatBalancedUnitary_sq_oai.{u_1, u_2}
