-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.exists_minimal_closed_subgroup_of_chain_condition
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:57:36.983981+00:00
-- url     : https://prove2.me/submissions/378253a1-0a2b-449c-9199-abdca65cafe9

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



/-- Zorn's lemma for a property of closed intermediate subgroups that survives
nonempty descending chains. The starting subgroup is the whole ambient group. -/
private theorem exists_minimal_closed_subgroup_of_chain_condition_preparedProof
    (P : Subgroup J) (bad : Subgroup J → Prop) (hbad : bad ⊤)
    (hchain : ∀ c : Set (Subgroup J), c.Nonempty → IsChain (· ≤ ·) c →
      (∀ H ∈ c, IsClosed (H : Set J) ∧ P ≤ H ∧ bad H) → bad (sInf c)) :
    ∃ L, Minimal (fun H : Subgroup J => IsClosed (H : Set J) ∧ P ≤ H ∧ bad H) L := by
  classical
  let S : Set (Subgroup J) := {H | IsClosed (H : Set J) ∧ P ≤ H ∧ bad H}
  have hb : ∀ c : Set (Subgroup J), c ⊆ S → IsChain (· ≤ ·) c →
      ∃ L ∈ S, ∀ H ∈ c, L ≤ H := by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with he | hn
    · subst c
      exact ⟨⊤, ⟨isClosed_univ, le_top, hbad⟩, by simp⟩
    · refine ⟨sInf c, ⟨?_, ?_, hchain c hn hc hcs⟩,
        fun H hH => sInf_le hH⟩
      · rw [Subgroup.coe_sInf]
        exact isClosed_biInter (fun H hH => (hcs hH).1)
      · exact le_sInf (fun H hH => (hcs hH).2.1)
  exact (@zorn_le₀ (Subgroup J)ᵒᵈ _ S) (fun c hcs hc => hb c hcs hc.symm)

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
  (P : @Subgroup.{u_1} J inst) (bad : @Subgroup.{u_1} J inst → Prop)
  (hbad : bad (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
  (hchain :
    ∀ (c : Set.{u_1} (@Subgroup.{u_1} J inst)),
      @Set.Nonempty.{u_1} (@Subgroup.{u_1} J inst) c →
        @IsChain.{u_1} (@Subgroup.{u_1} J inst)
            (fun (x1 x2 : @Subgroup.{u_1} J inst) =>
              @LE.le.{u_1} (@Subgroup.{u_1} J inst)
                (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                  (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
                x1 x2)
            c →
          (∀ (H : @Subgroup.{u_1} J inst),
              @Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
                  (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H →
                And
                  (@IsClosed.{u_1} J inst_1
                    (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
                  (And
                    (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
                      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                          (@Subgroup.instPartialOrder.{u_1} J inst)))
                      P H)
                    (bad H))) →
            bad (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c)),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (L : @Subgroup.{u_1} J inst) =>
    @Minimal.{u_1} (@Subgroup.{u_1} J inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
      (fun (H : @Subgroup.{u_1} J inst) =>
        And
          (@IsClosed.{u_1} J inst_1
            (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
          (And
            (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              P H)
            (bad H)))
      L :=
  @LocalConjugacy.Proof.LocalConjugacy.exists_minimal_closed_subgroup_of_chain_condition_preparedProof
