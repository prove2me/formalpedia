-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.prosupersolvable_hall_split_containing
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:07:54.916171+00:00
-- url     : https://prove2.me/submissions/415fd62c-3396-4cfa-ab41-87e8058a824c

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteSubgroupSystem_map_subgroup
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_HallComplementSystem_exists_compatible

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- Closed subgroups are separated by their images in finite continuous
quotients. This supplies the separation step of the compactness argument. -/
private theorem mem_of_mem_sup_openNormal (H : Subgroup G) (hH : IsClosed (H : Set G))
    (x : G) (hx : ∀ U : OpenNormalSubgroup G, x ∈ H ⊔ U.toSubgroup) : x ∈ H := by
  let HC : ClosedSubgroup G := { toSubgroup := H, isClosed' := hH }
  change x ∈ HC.toSubgroup
  rw [ProfiniteGrp.closedSubgroup_eq_sInf_open HC]
  apply Subgroup.mem_sInf.mpr
  intro V hV
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hV.1 V.one_mem
  exact (sup_le hV.2 hU) (hx U)





end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

namespace FiniteSubgroupSystem
open FiniteSylowSystem
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
variable (S : (U : OpenNormalSubgroup G) → Subgroup (G ⧸ U.toSubgroup))
variable (hS : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (S U).map (transition h) = S V)





private theorem subgroup_closed : IsClosed (subgroup S : Set G) := by
  rw [show (subgroup S : Set G) = ⋂ U : OpenNormalSubgroup G,
    (QuotientGroup.mk' U.toSubgroup) ⁻¹' (S U).carrier by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact mem_subgroup S x]
  apply isClosed_iInter
  intro U
  have hc : IsClosed (S U).carrier := isClosed_discrete _
  exact hc.preimage (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))

include hS








end FiniteSubgroupSystem

section ProfiniteHall
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
open FiniteSylowSystem
open scoped Pointwise

private theorem subgroup_le_of_finite_images (H K : Subgroup G) (hK : IsClosed (K : Set G))
    (h : ∀ U : OpenNormalSubgroup G,
      H.map (QuotientGroup.mk' U.toSubgroup) ≤ K.map (QuotientGroup.mk' U.toSubgroup)) :
    H ≤ K := by
  intro x hx
  apply mem_of_mem_sup_openNormal K hK x
  intro U
  have hm := h U (Subgroup.mem_map_of_mem (QuotientGroup.mk' U.toSubgroup) hx)
  change x ∈ (K.map (QuotientGroup.mk' U.toSubgroup)).comap (QuotientGroup.mk' U.toSubgroup) at hm
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hm

















private theorem upperHall_isHallPro (hG : Prosupersolvable G) (n : ℕ) :
    IsHallPro {p | n < p} (upperHall hG n) := by
  refine ⟨FiniteSubgroupSystem.subgroup_closed _, fun U => ?_⟩
  change IsHall _ ((FiniteSubgroupSystem.subgroup _).map _)
  rw [FiniteSubgroupSystem.map_subgroup _ (finiteUpperHall_transition hG n)]
  exact finiteUpperHall_hall hG n U

namespace HallComplementSystem
open CategoryTheory
variable (hG : Prosupersolvable G) (n : ℕ) (P : Subgroup G)









end HallComplementSystem

/-- The profinite Hall cutoff decomposition, including the requirement
that the complement contain a prescribed Sylow subgroup below the cutoff. -/
private theorem prosupersolvable_hall_split_containing_preparedProof (hG : Prosupersolvable G)
    {n p : ℕ} [Fact p.Prime] (hpn : p ≤ n) (P : Subgroup G) (hP : IsSylowPro p ⊤ P) :
    ∃ M Q : Subgroup G, M.Normal ∧ IsHallPro {r | n < r} M ∧
      IsHallPro {r | r ≤ n} Q ∧ M.IsComplement' Q ∧ P ≤ Q := by
  classical
  obtain ⟨Qs, hQs⟩ := HallComplementSystem.exists_compatible hG n P hpn hP
  let M := upperHall hG n
  let Q := FiniteSubgroupSystem.subgroup (fun U => (Qs U).val)
  have hM := upperHall_isHallPro hG n
  have hQclosed : IsClosed (Q : Set G) := FiniteSubgroupSystem.subgroup_closed _
  have hMmap (U : OpenNormalSubgroup G) :
      M.map (QuotientGroup.mk' U.toSubgroup) = finiteUpperHall hG n U :=
    FiniteSubgroupSystem.map_subgroup _ (finiteUpperHall_transition hG n) U
  have hQmap (U : OpenNormalSubgroup G) : Q.map (QuotientGroup.mk' U.toSubgroup) = (Qs U).val :=
    FiniteSubgroupSystem.map_subgroup _ hQs U
  have hQHall : IsHallPro {r | r ≤ n} Q := by
    refine ⟨hQclosed, fun U => ?_⟩
    rw [hQmap]
    exact (Qs U).property.2.1
  have hPQ : P ≤ Q := by
    apply subgroup_le_of_finite_images P Q hQclosed
    intro U
    rw [hQmap]
    exact (Qs U).property.2.2
  have hd : Disjoint M Q := by
    apply disjoint_iff_inf_le.mpr
    apply subgroup_le_of_finite_images (M ⊓ Q) ⊥ (isClosed_singleton : IsClosed ({1} : Set G))
    intro U
    have hh := Subgroup.map_mono (show M ⊓ Q ≤ M from inf_le_left) (f := QuotientGroup.mk' U.toSubgroup)
    have hk := Subgroup.map_mono (show M ⊓ Q ≤ Q from inf_le_right) (f := QuotientGroup.mk' U.toSubgroup)
    rw [hMmap] at hh
    rw [hQmap] at hk
    rw [Subgroup.map_bot]
    exact (le_inf hh hk).trans (Qs U).property.1.disjoint.le_bot
  have hsupclosed : IsClosed ((M ⊔ Q : Subgroup G) : Set G) := by
    rw [Subgroup.normal_mul]
    exact hQclosed.mul_left_of_isCompact hM.1.isCompact
  have hsup : M ⊔ Q = ⊤ := by
    apply top_unique
    apply subgroup_le_of_finite_images ⊤ (M ⊔ Q) hsupclosed
    intro U
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U.toSubgroup),
      Subgroup.map_sup, hMmap, hQmap, (Qs U).property.1.sup_eq_top]
  have hcomp : M.IsComplement' Q := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd
    rw [← Subgroup.normal_mul, hsup]
    rfl
  exact ⟨M, Q, inferInstance, hM, hQHall, hcomp, hPQ⟩

end ProfiniteHall
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1} G inst inst_1) {n p : Nat} [Fact (Nat.Prime p)]
  (hpn : @LE.le.{0} Nat instLENat p n) (P : @Subgroup.{u_1} G inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1
      (@Top.top.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instTop.{u_1} G inst)) P),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (M : @Subgroup.{u_1} G inst) =>
    @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (Q : @Subgroup.{u_1} G inst) =>
      And (@Subgroup.Normal.{u_1} G inst M)
        (And
          (@LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} G inst inst_1
            (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat n r) M)
          (And
            (@LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} G inst inst_1
              (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r n) Q)
            (And (@Subgroup.IsComplement'.{u_1} G inst M Q)
              (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
                (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
                  (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
                P Q)))) :=
  @LocalConjugacy.Proof.LocalConjugacy.prosupersolvable_hall_split_containing_preparedProof
