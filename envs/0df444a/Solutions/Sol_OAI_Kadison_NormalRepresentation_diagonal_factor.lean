-- Prove2me | solution 1 for OAI.Kadison.NormalRepresentation.diagonal_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:41:22.828995+00:00
-- url     : https://prove2.me/submissions/5ceb1f57-7473-40f6-b0ed-0187b34a3371

import Mathlib
import Definitions.Def_OAIQ039C062

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertBiprod
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

variable [CompleteSpace H] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

lemma diagHom_injective (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (hφ : Function.Injective φ) : Function.Injective (diagHom φ ψ) := by
  intro a b hab
  apply hφ
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun U : Space H G →L[ℂ] Space H G => (U (inl x)).ofLp.1) hab
  simpa using h

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RepresentedFactorTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.FactorCorner

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H)

lemma image_factor (hM : IsFactor M) (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G))
    (hinj : Function.Injective φ)
    (hclosed : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ) :
    IsFactor (BicommutantRange.ofStarHom φ hclosed) := by
  intro z hz hzc
  obtain ⟨a,rfl⟩ := hz
  have hac : (a:H →L[ℂ] H)∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
    intro b hb
    have he : (⟨b,hb⟩:M)*a=a*⟨b,hb⟩ := by
      apply hinj
      simp only [map_mul]
      exact hzc _ (Set.mem_range_self (⟨b,hb⟩:M))
    exact congrArg (fun c : M => (c:H →L[ℂ] H)) he
  obtain ⟨c,hc⟩ := hM a a.property hac
  have ha : a=c • (1:M) := Subtype.ext hc
  refine ⟨c,?_⟩
  change φ a=c • 1
  rw [ha,map_smul,map_one]

end Kadison.FactorCorner

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

lemma diagonal_factor_oai (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hM : FactorCorner.IsFactor M) : FactorCorner.IsFactor (diagonalAlgebra M τ hnormal) :=
  FactorCorner.image_factor M hM _
    (diagHom_injective M.toStarSubalgebra.subtype τ.gnsStarAlgHom Subtype.val_injective)
    (NormalOperatorHom.diagonal_gns_range M τ hnormal)

end Kadison.NormalRepresentation

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalRepresentation.diagonal_factor_oai.{u_1} := @OAI.Kadison.NormalRepresentation.diagonal_factor_oai.{u_1}
