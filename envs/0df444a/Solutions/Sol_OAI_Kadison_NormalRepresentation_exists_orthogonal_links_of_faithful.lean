-- Prove2me | solution 1 for OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:43:16.527834+00:00
-- url     : https://prove2.me/submissions/28fb655c-1f99-4f5a-a4b7-fb8c678c794c

import Mathlib
import Definitions.Def_OAIQ039C062
import Theorems.Thm_OAI_Kadison_NormalRepresentation_right_full_central_support
import Theorems.Thm_OAI_Kadison_NormalRepresentation_right_mem_commutant
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_maximal_family_spans_of_full_support

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
lemma left_commutes (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block S T*left=left*block S T := by
  rw [left,←block_mul,←block_mul]
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

lemma left_mem_diagonal_commutant :
    left (H:=H) (G:=G)∈(BicommutantRange.ofStarHom (H:=Space H G) (diagHom φ ψ) h).commutant := by
  rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
  rintro _ ⟨a,rfl⟩
  exact left_commutes _ _

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrthogonalLinkFamily
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

lemma exists_maximal_orthogonalLinks :
    ∃ S : Set (Link M e f),Maximal (OrthogonalLinks M e f) S := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c,?_,fun s hs => Set.subset_sUnion_of_mem hs⟩
  intro v hv w hw hne
  obtain ⟨s,hs,hvs⟩ := hv
  obtain ⟨t,ht,hwt⟩ := hw
  rcases hchain.total hs ht with hst|hts
  · exact hc ht (hst hvs) hwt hne
  · exact hc hs hvs (hts hwt) hne

end Kadison.PartialIsometryOrder

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

lemma left_mem_commutant (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    left (H:=H) (G:=τ.GNS)∈(diagonalAlgebra M τ hnormal).commutant :=
  left_mem_diagonal_commutant (A:=M) (H:=H) (G:=τ.GNS)
    M.toStarSubalgebra.subtype τ.gnsStarAlgHom (NormalOperatorHom.diagonal_gns_range M τ hnormal)

end Kadison.NormalRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulNormalRepresentationLinks
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

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem exists_orthogonal_links_of_faithful_oai
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
    ∃ S : Set (Link (diagonalAlgebra M τ hnormal).commutant
      (right (H:=H) (G:=τ.GNS)) left),
      OrthogonalLinks _ _ _ S ∧ (familySpace _ _ _ S).starProjection=left := by
  obtain ⟨S,hS⟩ := exists_maximal_orthogonalLinks (diagonalAlgebra M τ hnormal).commutant
    (right (H:=H) (G:=τ.GNS)) left
  refine ⟨S,hS.1,?_⟩
  exact maximal_family_spans_of_full_support _ _ _
    (right_full_central_support M τ hnormal hfaith)
    (right_mem_commutant M τ hnormal) (left_mem_commutant M τ hnormal)
    right_projection left_projection S hS

end Kadison.NormalRepresentation

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful_oai.{u_1} := @OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful_oai.{u_1}
