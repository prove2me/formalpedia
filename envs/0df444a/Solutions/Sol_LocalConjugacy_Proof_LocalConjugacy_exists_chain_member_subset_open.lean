-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.exists_chain_member_subset_open
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:39:26.377334+00:00
-- url     : https://prove2.me/submissions/6a9a0f7d-21b5-45bf-b1bf-96f48e0c6d2c

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

section Compactness
variable {J : Type*} [Group J] [TopologicalSpace J] [CompactSpace J]

/-- A descending chain of closed subgroups eventually lies in every open set
containing its intersection. Chains need not be countable. -/
private theorem exists_chain_member_subset_open_preparedProof (c : Set (Subgroup J)) (hne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) (hclosed : ∀ H ∈ c, IsClosed (H : Set J))
    (O : Set J) (hO : IsOpen O) (hsub : ((sInf c : Subgroup J) : Set J) ⊆ O) :
    ∃ H ∈ c, (H : Set J) ⊆ O := by
  classical
  letI : Nonempty c := hne.to_subtype
  have hd : Directed (· ⊇ ·) (fun H : c => (H.val : Set J)) := by
    intro H K
    rcases hc.total H.property K.property with h | h
    · exact ⟨H, le_rfl, h⟩
    · exact ⟨K, h, le_rfl⟩
  have hempty : Oᶜ ∩ (⋂ H : c, (H.val : Set J)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hi⟩
    apply hx (hsub ?_)
    exact Subgroup.mem_sInf.mpr (fun H hH => Set.mem_iInter.mp hi ⟨H, hH⟩)
  obtain ⟨H, hH⟩ := hO.isClosed_compl.isCompact.elim_directed_family_closed
    (fun H : c => (H.val : Set J)) (fun H => hclosed H H.property)
    hempty hd
  refine ⟨H, H.property, fun x hx => ?_⟩
  by_contra hn
  exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hH) hn hx



end Compactness

section Extension
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]







end Extension

section Obstructions
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]















end Obstructions

section Invariance
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



end Invariance
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J] [@CompactSpace.{u_1} J inst_1]
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
        @IsClosed.{u_1} J inst_1
          (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
  (O : Set.{u_1} J) (hO : @IsOpen.{u_1} J inst_1 O)
  (hsub :
    @LE.le.{u_1} (Set.{u_1} J) (@Set.instLE.{u_1} J)
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)
        (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c))
      O),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (H : @Subgroup.{u_1} J inst) =>
    And
      (@Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
        (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H)
      (@LE.le.{u_1} (Set.{u_1} J) (@Set.instLE.{u_1} J)
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H) O) :=
  @LocalConjugacy.Proof.LocalConjugacy.exists_chain_member_subset_open_preparedProof
