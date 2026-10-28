-- Prove2me | solution 1 for OAI.Kadison.NormalRepresentation.right_mem_commutant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:46:16.562822+00:00
-- url     : https://prove2.me/submissions/780214b5-5b8d-40f8-af58-5220d0af6862

import Mathlib
import Definitions.Def_OAIQ039C062

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertBiprodProjections
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace H] [CompleteSpace G] in
lemma right_commutes (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block S T*right=right*block S T := by
  rw [right,←block_mul,←block_mul]
  simp

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiagonalBlockCommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

variable (h : Set.centralizer (Set.centralizer (Set.range (diagHom φ ψ)))=Set.range (diagHom φ ψ))

lemma right_mem_diagonal_commutant :
    right (H:=H) (G:=G)∈(BicommutantRange.ofStarHom (H:=Space H G) (diagHom φ ψ) h).commutant := by
  rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
  rintro _ ⟨a,rfl⟩
  exact right_commutes _ _

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalRepresentationLinks
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

open HilbertBiprod PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma right_mem_commutant_oai (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    right (H:=H) (G:=τ.GNS)∈(diagonalAlgebra M τ hnormal).commutant :=
  right_mem_diagonal_commutant (A:=M) (H:=H) (G:=τ.GNS)
    M.toStarSubalgebra.subtype τ.gnsStarAlgHom (NormalOperatorHom.diagonal_gns_range M τ hnormal)

end Kadison.NormalRepresentation

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalRepresentation.right_mem_commutant_oai.{u_1} := @OAI.Kadison.NormalRepresentation.right_mem_commutant_oai.{u_1}
