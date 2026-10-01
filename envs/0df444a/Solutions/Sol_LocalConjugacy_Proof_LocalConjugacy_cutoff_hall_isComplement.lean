-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.cutoff_hall_isComplement
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:52:07.84192+00:00
-- url     : https://prove2.me/submissions/0b24af0c-21f5-4950-bf93-8418e5227719

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



















namespace HallComplementSystem
open CategoryTheory
variable (hG : Prosupersolvable G) (n : ℕ) (P : Subgroup G)









end HallComplementSystem



end ProfiniteHall
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-!
Proposition 2.3 (`prop:res_pi`) of the current manuscript. The Hall subgroup
`Q` is arbitrary, not just the complement chosen in a structural existence
theorem. The proof follows the paper: construct the normal high-prime factor
`M`, show that it centralizes `N`, and extend by `φ(mq) = φ(q)`.
-/

namespace LocalConjugacy

/-- Complementary Hall subgroups, one normal, give the required profinite split. -/
private theorem cutoff_hall_isComplement_preparedProof
    {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]
    {p : ℕ} (M Q : Subgroup J) [M.Normal]
    (hM : IsHallPro {r | p < r} M) (hQ : IsHallPro {r | r ≤ p} Q) :
    M.IsComplement' Q := by
  have hd : Disjoint M Q := by
    apply disjoint_iff_inf_le.mpr
    apply subgroup_le_of_finite_images (M ⊓ Q) ⊥
      (isClosed_singleton : IsClosed ({1} : Set J))
    intro U
    rw [Subgroup.map_bot]
    exact (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)).trans
      (disjoint_of_cutoff_primes (hM.2 U).1 (hQ.2 U).1).le_bot
  have hclosed : IsClosed ((M ⊔ Q : Subgroup J) : Set J) := by
    rw [Subgroup.normal_mul]
    exact hQ.1.mul_left_of_isCompact hM.1.isCompact
  have hsup : M ⊔ Q = ⊤ := by
    apply top_unique
    apply subgroup_le_of_finite_images ⊤ (M ⊔ Q) hclosed
    intro U
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U.toSubgroup),
      Subgroup.map_sup]
    apply le_of_eq
    symm
    apply Subgroup.index_eq_one.mp
    by_contra hn
    obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd hn
    have hm := (hM.2 U).2 r hr (hd.trans (Subgroup.index_dvd_of_le le_sup_left))
    have hq := (hQ.2 U).2 r hr (hd.trans (Subgroup.index_dvd_of_le le_sup_right))
    exact hq (Nat.le_of_not_gt hm)
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd
  rw [← Subgroup.normal_mul, hsup]
  rfl

section Numbered
variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N]



end Numbered
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_1] {p : Nat} (M Q : @Subgroup.{u_1} J inst)
  [@Subgroup.Normal.{u_1} J inst M]
  (hM :
    @LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_1
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat p r) M)
  (hQ :
    @LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_1
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r p) Q),
  @Subgroup.IsComplement'.{u_1} J inst M Q :=
  @LocalConjugacy.Proof.LocalConjugacy.cutoff_hall_isComplement_preparedProof
