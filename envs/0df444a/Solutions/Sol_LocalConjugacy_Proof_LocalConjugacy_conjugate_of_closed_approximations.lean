-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.conjugate_of_closed_approximations
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:45:53.537094+00:00
-- url     : https://prove2.me/submissions/b9f77d9f-21fd-4cd7-9eae-5ec6f1bf92b3

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

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]



private theorem transporter_closed (H K : Subgroup G) (hK : IsClosed (K : Set G)) :
    IsClosed (transporter H K) := by
  unfold transporter
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun h => isClosed_iInter fun _ =>
    hK.preimage ((continuous_id.mul continuous_const).mul continuous_inv)

/-- The compactness step in Theorem 1.1. It applies to the paper's
`Hᵢ = (N ∩ Uᵢ)H` and `Kᵢ = (N ∩ Uᵢ)K` once the finite-quotient and
separation lemmas have been proved. All approximation hypotheses remain
explicit; this is not a claimed proof of Theorem 1.1 itself. -/
private theorem conjugate_of_closed_approximations_preparedProof [CompactSpace G]
    {ι : Type*} [Nonempty ι] (H K : Subgroup G) (Hs Ks : ι → Subgroup G)
    (hHclosed : ∀ i, IsClosed (Hs i : Set G))
    (hKclosed : ∀ i, IsClosed (Ks i : Set G))
    (hHsep : ∀ x : G, (∀ i, x ∈ Hs i) → x ∈ H)
    (hKsep : ∀ x : G, (∀ i, x ∈ Ks i) → x ∈ K)
    (hdir : ∀ i j, ∃ k, Hs k ≤ Hs i ∧ Hs k ≤ Hs j ∧ Ks k ≤ Ks i ∧ Ks k ≤ Ks j)
    (hloc : ∀ i, ∃ g : G, g ∈ transporter H (Ks i) ∧ g⁻¹ ∈ transporter K (Hs i)) :
    Conjugate H K := by
  let T : ι → Set G := fun i => transporter H (Ks i) ∩ Inv.inv ⁻¹' transporter K (Hs i)
  have hclosed : ∀ i, IsClosed (T i) := fun i =>
    (transporter_closed H (Ks i) (hKclosed i)).inter
      ((transporter_closed K (Hs i) (hHclosed i)).preimage continuous_inv)
  have hnon : ∀ i, (T i).Nonempty := fun i => hloc i
  have hTdir : Directed (· ⊇ ·) T := by
    intro i j
    obtain ⟨k, hki, hkj, kki, kkj⟩ := hdir i j
    refine ⟨k, ?_, ?_⟩
    · intro g hg
      exact ⟨fun x hx => kki (hg.1 x hx), fun x hx => hki (hg.2 x hx)⟩
    · intro g hg
      exact ⟨fun x hx => kkj (hg.1 x hx), fun x hx => hkj (hg.2 x hx)⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hTdir hnon (fun i => (hclosed i).isCompact) hclosed
  have hg' : ∀ i, g ∈ T i := Set.mem_iInter.mp hg
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hKsep _ (fun i => (hg' i).1 x hx)
  · intro y hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · apply hHsep
      intro i
      simpa using (hg' i).2 y hy
    · change g * (g⁻¹ * y * g) * g⁻¹ = y
      group

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G] [@IsTopologicalGroup.{u_1} G inst_1 inst]
  [@CompactSpace.{u_1} G inst_1] {ι : Type u_2} [Nonempty.{u_2 + 1} ι] (H K : @Subgroup.{u_1} G inst)
  (Hs Ks : ι → @Subgroup.{u_1} G inst)
  (hHclosed :
    ∀ (i : ι),
      @IsClosed.{u_1} G inst_1
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) (Hs i)))
  (hKclosed :
    ∀ (i : ι),
      @IsClosed.{u_1} G inst_1
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) (Ks i)))
  (hHsep :
    ∀ (x : G),
      (∀ (i : ι),
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) (Hs i)
            x) →
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
  (hKsep :
    ∀ (x : G),
      (∀ (i : ι),
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) (Ks i)
            x) →
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
  (hdir :
    ∀ (i j : ι),
      @Exists.{u_2 + 1} ι fun (k : ι) =>
        And
          (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
            (Hs k) (Hs i))
          (And
            (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
              (Hs k) (Hs j))
            (And
              (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
                (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
                  (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
                (Ks k) (Ks i))
              (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
                (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
                  (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
                (Ks k) (Ks j)))))
  (hloc :
    ∀ (i : ι),
      @Exists.{u_1 + 1} G fun (g : G) =>
        And
          (@Membership.mem.{u_1, u_1} G (Set.{u_1} G) (@Set.instMembership.{u_1} G)
            (@LocalConjugacy.Proof.LocalConjugacy.transporter.{u_1} G inst H (Ks i)) g)
          (@Membership.mem.{u_1, u_1} G (Set.{u_1} G) (@Set.instMembership.{u_1} G)
            (@LocalConjugacy.Proof.LocalConjugacy.transporter.{u_1} G inst K (Hs i))
            (@Inv.inv.{u_1} G
              (@InvOneClass.toInv.{u_1} G
                (@DivInvOneMonoid.toInvOneClass.{u_1} G
                  (@DivisionMonoid.toDivInvOneMonoid.{u_1} G (@Group.toDivisionMonoid.{u_1} G inst))))
              g))),
  @LocalConjugacy.Proof.LocalConjugacy.Conjugate.{u_1} G inst H K :=
  @LocalConjugacy.Proof.LocalConjugacy.conjugate_of_closed_approximations_preparedProof
