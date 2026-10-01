-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_pi
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:00:53.371907+00:00
-- url     : https://prove2.me/submissions/5d8153d5-f2e1-44c7-ad96-062bd8afb4f9

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]



/-- The first clause of primary decomposition requires no finiteness,
nilpotence, or solvability assumption. -/
private theorem primary_restriction_is_stable (P : PrimeDivisor J → Subgroup J)
    (f : Cocycle (N := N) (⊤ : Subgroup J)) (p : PrimeDivisor J) :
    InvariantUnder ⊤ (P p) (restrictCocycle le_top f) :=
  invariant_restriction (P p) f

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Products
variable {J : Type*} [Group J] [TopologicalSpace J]
  {ι : Type*} {N : ι → Type*} [∀ i, Group (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, MulDistribMulAction J (N i)]

namespace Cocycle





end Cocycle

private theorem cohomologous_pi_iff {K : Subgroup J} (f g : Cocycle (N := ∀ i, N i) K) :
    Cohomologous f g ↔ ∀ i, Cohomologous (f.component i) (g.component i) := by
  constructor
  · rintro ⟨n, hn⟩ i
    exact ⟨n i, fun x => congrFun (hn x) i⟩
  · intro h
    choose n hn using h
    exact ⟨n, fun x => funext fun i => hn i x⟩

private theorem invariant_pi_iff {L K : Subgroup J} (f : Cocycle (N := ∀ i, N i) K) :
    InvariantUnder L K f ↔ ∀ i, InvariantUnder L K (f.component i) := by
  constructor
  · intro h i j hj
    obtain ⟨n, hn⟩ := h j hj
    exact ⟨n i, fun x hx hjx => congrFun (hn x hx hjx) i⟩
  · intro h j hj
    choose n hn using fun i => h i j hj
    exact ⟨n, fun x hx hjx => funext fun i => hn i x hx hjx⟩

private theorem primaryDecomposition_pi_preparedProof (P : PrimeDivisor J → Subgroup J)
    (h : ∀ i, PrimaryDecomposition (N := N i) P) :
    PrimaryDecomposition (N := ∀ i, N i) P := by
  classical
  refine ⟨primary_restriction_is_stable P, ?_, ?_⟩
  · intro f g hr
    apply (cohomologous_pi_iff f g).mpr
    intro i
    apply (h i).2.1 (f.component i) (g.component i)
    intro p
    obtain ⟨n, hn⟩ := hr p
    exact ⟨n i, fun x => congrFun (hn x) i⟩
  · intro f hf
    have hi (i : ι) : ∃ g : Cocycle (N := N i) (⊤ : Subgroup J),
        ∀ p, RestrictsTo (show P p ≤ ⊤ from le_top) g ((f p).component i) :=
      (h i).2.2 (fun p => (f p).component i)
        (fun p => (invariant_pi_iff (f p)).mp (hf p) i)
    choose g hg using hi
    refine ⟨Cocycle.pi g, fun p => ?_⟩
    choose n hn using fun i => hg i p
    exact ⟨n, fun x => funext fun i => hn i x⟩

end Products

section Coefficients
variable {J N M : Type*} [Group J] [Group N] [Group M]
  [TopologicalSpace J] [TopologicalSpace N] [TopologicalSpace M]
  [MulDistribMulAction J N] [MulDistribMulAction J M]

namespace Cocycle



end Cocycle







end Coefficients
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2 u_3

theorem solution :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J] {ι : Type u_2} {N : ι → Type u_3}
  [inst_2 : (i : ι) → Group.{u_3} (N i)] [inst_3 : (i : ι) → TopologicalSpace.{u_3} (N i)]
  [inst_4 :
    (i : ι) →
      @MulDistribMulAction.{u_1, u_3} J (N i) (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
        (@DivInvMonoid.toMonoid.{u_3} (N i) (@Group.toDivInvMonoid.{u_3} (N i) (inst_2 i)))]
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_1 → @Subgroup.{u_1} J inst)
  (h :
    ∀ (i : ι),
      @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_3} J (N i) inst (inst_2 i) inst_1 (inst_3 i)
        (inst_4 i) P),
  @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, max u_2 u_3} J ((i : ι) → N i) inst
    (@Pi.group.{u_2, u_3} ι N inst_2) inst_1 (@Pi.topologicalSpace.{u_3, u_2} ι N inst_3)
    (@Pi.mulDistribMulAction.{u_2, u_3, u_1} ι N J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (fun (i : ι) =>
        @DivInvMonoid.toMonoid.{u_3} (N i) ((fun (i : ι) => @Group.toDivInvMonoid.{u_3} (N i) (inst_2 i)) i))
      inst_4)
    P :=
  @LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_pi_preparedProof
