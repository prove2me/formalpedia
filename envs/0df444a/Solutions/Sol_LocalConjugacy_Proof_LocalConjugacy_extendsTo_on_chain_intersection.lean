-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.extendsTo_on_chain_intersection
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:10:37.887848+00:00
-- url     : https://prove2.me/submissions/02668a33-2a46-4605-9ffc-a8a65cb4d653

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_chain_member_subset_open
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_extend_cocycle_to_open_subgroup

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Compactness
variable {J : Type*} [Group J] [TopologicalSpace J] [CompactSpace J]





end Compactness

section Extension
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]





/-- An extension restricts to any intermediate subgroup containing the original domain. -/
private theorem Cocycle.ExtendsTo.of_le {P H K : Subgroup J} {f : Cocycle (N := N) P}
    (h : f.ExtendsTo K) (hPH : P ≤ H) (hHK : H ≤ K) : f.ExtendsTo H := by
  obtain ⟨_, F, n, hn⟩ := h
  exact ⟨hPH, restrictCocycle hHK F, n, hn⟩

end Extension

section Obstructions
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





/-- If a fixed cocycle class extends to the intersection of a descending
chain, it extends to one member. The proof extends a representative to an
open neighborhood subgroup, so it permits infinite discrete coefficients. -/
private theorem extendsTo_on_chain_intersection_preparedProof {P : Subgroup J} (f : Cocycle (N := N) P)
    (c : Set (Subgroup J)) (hne : c.Nonempty) (hc : IsChain (· ≤ ·) c)
    (hclosed : ∀ H ∈ c, IsClosed (H : Set J)) (hP : ∀ H ∈ c, P ≤ H)
    (hf : f.ExtendsTo (sInf c)) : ∃ H ∈ c, f.ExtendsTo H := by
  have hi : IsClosed ((sInf c : Subgroup J) : Set J) := by
    rw [Subgroup.coe_sInf]
    exact isClosed_biInter hclosed
  obtain ⟨hPi, F, hF⟩ := hf
  obtain ⟨V, hVi, hV, G, hG⟩ := extend_cocycle_to_open_subgroup (sInf c) hi F
  have hfV : f.ExtendsTo V := by
    refine ⟨hPi.trans hVi, G, ?_⟩
    change Cohomologous (restrictCocycle (hPi.trans hVi) G) f
    change Cohomologous (restrictCocycle hPi (restrictCocycle hVi G)) f
    rw [hG]
    exact hF
  obtain ⟨H, hH, hHV⟩ := exists_chain_member_subset_open c hne hc hclosed V hV hVi
  exact ⟨H, hH, hfV.of_le (hP H hH) hHV⟩









end Obstructions

section Invariance
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



end Invariance
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  {P : @Subgroup.{u_1} J inst}
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P)
  (c : Set.{u_1} (@Subgroup.{u_1} J inst)) (hne : @Set.Nonempty.{u_1} (@Subgroup.{u_1} J inst) c)
  (hc :
    @IsChain.{u_1} (@Subgroup.{u_1} J inst)
      (fun (x1 x2 : @Subgroup.{u_1} J inst) =>
        @LE.le.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          x1 x2)
      c)
  (hclosed :
    ∀ (H : @Subgroup.{u_1} J inst),
      @Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
          (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H →
        @IsClosed.{u_1} J inst_2
          (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
  (hP :
    ∀ (H : @Subgroup.{u_1} J inst),
      @Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
          (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H →
        @LE.le.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          P H)
  (hf :
    @LocalConjugacy.Proof.LocalConjugacy.Cocycle.ExtendsTo.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P f
      (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c)),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (H : @Subgroup.{u_1} J inst) =>
    And
      (@Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
        (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H)
      (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.ExtendsTo.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P f H) :=
  @LocalConjugacy.Proof.LocalConjugacy.extendsTo_on_chain_intersection_preparedProof
