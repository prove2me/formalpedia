-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.cohomologous_on_chain_intersection
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:46:48.414271+00:00
-- url     : https://prove2.me/submissions/3b0e05cf-1b22-4b55-94f5-c2855b0d26a2

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







end Extension

section Obstructions
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- If a fixed pair of global cocycles becomes cohomologous on a chain's
intersection, it is already cohomologous on one member of the chain. -/
private theorem cohomologous_on_chain_intersection_preparedProof
    (f g : Cocycle (N := N) (⊤ : Subgroup J))
    (c : Set (Subgroup J)) (hne : c.Nonempty) (hc : IsChain (· ≤ ·) c)
    (hclosed : ∀ H ∈ c, IsClosed (H : Set J))
    (hfg : Cohomologous (restrictCocycle (show sInf c ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g)) :
    ∃ H ∈ c, Cohomologous (restrictCocycle (show H ≤ ⊤ from le_top) f)
      (restrictCocycle le_top g) := by
  obtain ⟨n, hn⟩ := hfg
  let E : Set J := {x | g.toFun ⟨x, trivial⟩ =
    n⁻¹ * f.toFun ⟨x, trivial⟩ * (x • n)}
  have he : IsOpen E := by
    have htop : Continuous (fun x : J => (⟨x, trivial⟩ : (⊤ : Subgroup J))) :=
      continuous_id.subtype_mk _
    have ht : Continuous (fun x : J =>
        (g.toFun ⟨x, trivial⟩, f.toFun ⟨x, trivial⟩, x • n)) :=
      (g.continuous_toFun.comp htop).prodMk
        ((f.continuous_toFun.comp htop).prodMk (continuous_id.smul continuous_const))
    exact ht.isOpen_preimage
      {t : N × N × N | t.1 = n⁻¹ * t.2.1 * t.2.2} (isOpen_discrete _)
  have hs : ((sInf c : Subgroup J) : Set J) ⊆ E := fun x hx => hn ⟨x, hx⟩
  obtain ⟨H, hH, hHE⟩ := exists_chain_member_subset_open c hne hc hclosed E he hs
  exact ⟨H, hH, n, fun x => hHE x.property⟩













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
  (f g :
    @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
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
  (hfg :
    @LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
      (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c)
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
        (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c)
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
        (have this :
          @LE.le.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c)
            (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
          @le_top.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))
            (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c);
        this)
        f)
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
        (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c)
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
          (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))))
        (@le_top.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
              (@Subgroup.instCompleteLattice.{u_1} J inst)))
          (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c))
        g)),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (H : @Subgroup.{u_1} J inst) =>
    And
      (@Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
        (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H)
      (@LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H
        (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H
          (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
          (have this :
            @LE.le.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              H (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
            @le_top.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                  (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
                (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                  (@Subgroup.instCompleteLattice.{u_1} J inst)))
              H;
          this)
          f)
        (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H
          (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
            (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                  (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
                (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                  (@Subgroup.instCompleteLattice.{u_1} J inst)))))
          (@le_top.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))
            H)
          g)) :=
  @LocalConjugacy.Proof.LocalConjugacy.cohomologous_on_chain_intersection_preparedProof
