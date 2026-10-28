-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.generatedFreeAlgebra_natural_of_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:28:02.929003+00:00
-- url     : https://prove2.me/submissions/4c43760a-6b46-4bb6-8c28-6c657e1307e2

import Mathlib
import Definitions.Def_OAIQ039C072
import Theorems.Thm_OAI_Kadison_TracialSequence_constantAction_apply

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedFreePair
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.GeneratedFreePair

open FreeMoments

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (D : VonNeumannAlgebra H) (k : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma le_ambient (M : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
    (hkM : ∀ a : A,k a∈M) : (algebra D k).toStarSubalgebra≤M.toStarSubalgebra := by
  intro a ha
  change a∈(M : Set (H →L[ℂ] H))
  rw [←M.centralizer_centralizer]
  have hb := (NormalGNS.mem_bicommutant _ _).mp ha
  have hj : D.toStarSubalgebra⊔k.range≤M.toStarSubalgebra := sup_le hDM (by
    rintro b ⟨x,rfl⟩
    exact hkM x)
  intro T hT
  apply hb T
  intro x hx
  exact hT x (hj hx)

lemma in_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hD : ∀ d : D,(d:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hk : ∀ a : A,k a∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (a : algebra D k) : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  have hle := le_ambient D k (NormalGNS.bicommutant S)
    (fun d hd => (NormalGNS.mem_bicommutant _ _).mpr (hD ⟨d,hd⟩))
    (fun b => (NormalGNS.mem_bicommutant _ _).mpr (hk b))
  exact (NormalGNS.mem_bicommutant _ _).mp (hle a.property)

lemma in_range_bicommutant {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (l : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hD : ∀ d : D,(d:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (Set.range l)))
    (hk : ∀ a : A,k a∈Set.range l)
    (a : algebra D k) : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (Set.range l)) := by
  exact in_bicommutant D k l.range hD
    (fun b => Set.subset_centralizer_centralizer (hk b)) a

end Kadison.GeneratedFreePair

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialGeneratedAlgebra
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialSequence

lemma generatedFreeAlgebra_natural
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω))
    (hD : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (a : generatedFreeAlgebra τ ω D) :
    (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))) := by
  dsimp only [generatedFreeAlgebra] at a
  have constant_range (value : A) : constantAction τ ω value ∈ Set.range (leftRestricted τ ω) :=
    ⟨constantSequence value, (constantAction_apply τ ω value).symm⟩
  with_reducible
    exact GeneratedFreePair.in_range_bicommutant (H := boundedSubspace τ ω) (A := A)
      (B := BoundedContinuousFunction ℕ A) D (constantAction τ ω) (leftRestricted τ ω)
      hD constant_range a

lemma generatedFreeAlgebra_natural_of_range_oai
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω))
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
    (hD : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (a : generatedFreeAlgebra τ ω D) :
    (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))) := by
  apply generatedFreeAlgebra_natural τ ω D
  intro operator
  apply Set.subset_centralizer_centralizer
  exact Set.range_comp_subset_range (mapSequence j) (leftRestricted τ ω) (hD operator)

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.generatedFreeAlgebra_natural_of_range_oai := @OAI.Kadison.TracialSequence.generatedFreeAlgebra_natural_of_range_oai
