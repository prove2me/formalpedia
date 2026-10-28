-- Prove2me | solution 1 for OAI.Kadison.CyclicSpatial.matrixRepresentation_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:22:52.725893+00:00
-- url     : https://prove2.me/submissions/51df3155-7c80-474d-8c5d-17ef87d7a165

import Mathlib
import Definitions.Def_OAIQ039C022

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpatialImplementation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicSpatial

open OperatorAmplification CyclicColumns ReducingRepresentation

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

attribute [local instance] OAI.Kadison.CyclicSpatial.instDecidableEq_solutions
lemma matrixRepresentation_norm_eq_oai (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hlam : Function.Injective lam) (X : CStarMatrix ι ι A) :
    ‖matrixRepresentation lam X‖=‖X‖ :=
  NonUnitalStarAlgHom.norm_map (matrixRepresentation (ι:=ι) lam).toNonUnitalStarAlgHom
    (matrixRepresentation_injective lam hlam) X

end Kadison.CyclicSpatial

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.CyclicSpatial.matrixRepresentation_norm_eq_oai.{u_1, u_2, u_3} := @OAI.Kadison.CyclicSpatial.matrixRepresentation_norm_eq_oai.{u_1, u_2, u_3}
