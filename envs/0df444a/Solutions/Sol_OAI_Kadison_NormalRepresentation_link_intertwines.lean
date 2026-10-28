-- Prove2me | solution 1 for OAI.Kadison.NormalRepresentation.link_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:45:08.929698+00:00
-- url     : https://prove2.me/submissions/199d8e12-eff1-4817-beb3-663653671917

import Mathlib
import Definitions.Def_OAIQ039C062
import Theorems.Thm_OAI_Kadison_BiprodLinkColumn_component_intertwines

section
-- module Solutions.OAIQ039_CM.Commutator_NormalRepresentationColumns
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder BiprodLinkColumn OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hnormal : NormalGNS.BoundedWOTContinuous M τ)

lemma link_intertwines_oai (v : Intertwiner (diagonalAlgebra M τ hnormal).commutant) (a : M) :
    (component _ v).comp (a:H →L[ℂ] H)=(τ.gnsStarAlgHom a).comp (component _ v) := by
  apply component_intertwines _ M.toStarSubalgebra.subtype τ.gnsStarAlgHom v a
  have hv : star v.val ∈ (diagonalAlgebra M τ hnormal).commutant :=
    (diagonalAlgebra M τ hnormal).commutant.star_mem' v.mem
  have ha : block (a:H →L[ℂ] H) (τ.gnsStarAlgHom a)∈diagonalAlgebra M τ hnormal := by
    exact ⟨a,rfl⟩
  rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant] at hv
  exact hv _ ha

end Kadison.NormalRepresentation

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalRepresentation.link_intertwines_oai.{u_1} := @OAI.Kadison.NormalRepresentation.link_intertwines_oai.{u_1}
