-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.conjugate_of_normal_intersection_quotients
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:51:54.376312+00:00
-- url     : https://prove2.me/submissions/9f773df3-cda8-4ad6-bf6e-b6c5dd84198a

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_of_closed_approximations

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

/-! The reductions needed to run Proposition 3.2's induction on `|N|`
while the ambient profinite group is allowed to be infinite. -/

namespace LocalConjugacy

section Algebra
variable {G : Type*} [Group G]









end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Profinite F]







end Topology

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

private theorem closed_sup_normal (D H : Subgroup G) [D.Normal]
    (hD : IsClosed (D : Set G)) (hH : IsClosed (H : Set G)) :
    IsClosed ((D ⊔ H : Subgroup G) : Set G) := by
  rw [Subgroup.normal_mul]
  exact hH.mul_left_of_isCompact hD.isCompact







end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The precise compactness system in Theorem 1.1: the quotients are by
`N ∩ U`, and their normal subgroups have finite order, although the quotients
themselves need not be finite. -/

namespace LocalConjugacy
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]



/-- Compactness of the conjugating-element sets for `G/(N ∩ U)`. -/
private theorem conjugate_of_normal_intersection_quotients_preparedProof (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (hquot : ∀ U : OpenNormalSubgroup G,
      Conjugate (H.map (QuotientGroup.mk' (N ⊓ U.toSubgroup)))
        (K.map (QuotientGroup.mk' (N ⊓ U.toSubgroup)))) : Conjugate H K := by
  let : Nonempty (OpenNormalSubgroup G) := ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩
  apply conjugate_of_closed_approximations H K
    (fun U : OpenNormalSubgroup G => H ⊔ (N ⊓ U.toSubgroup))
    (fun U : OpenNormalSubgroup G => K ⊔ (N ⊓ U.toSubgroup))
  · intro U
    rw [sup_comm]
    exact closed_sup_normal _ H (hN.inter U.isClosed) hH
  · intro U
    rw [sup_comm]
    exact closed_sup_normal _ K (hN.inter U.isClosed) hK
  · intro x hx
    exact mem_of_mem_sup_openNormal H hH x
      (fun U => (sup_le_sup_left inf_le_right H) (hx U))
  · intro x hx
    exact mem_of_mem_sup_openNormal K hK x
      (fun U => (sup_le_sup_left inf_le_right K) (hx U))
  · intro U V
    exact ⟨U ⊓ V, sup_le_sup_left (inf_le_inf_left N inf_le_left) H,
      sup_le_sup_left (inf_le_inf_left N inf_le_right) H,
      sup_le_sup_left (inf_le_inf_left N inf_le_left) K,
      sup_le_sup_left (inf_le_inf_left N inf_le_right) K⟩
  · intro U
    let D := N ⊓ U.toSubgroup
    let π := QuotientGroup.mk' D
    obtain ⟨q, hq⟩ := hquot U
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
    have hmem (L : Subgroup G) (x : G) : π x ∈ L.map π ↔ x ∈ L ⊔ D := by
      change x ∈ (L.map π).comap π ↔ _
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    refine ⟨g, ?_, ?_⟩
    · intro x hx
      apply (hmem K _).mp
      rw [← hq]
      exact Subgroup.mem_map.mpr ⟨π x, Subgroup.mem_map_of_mem π hx, by
        simp [π, MulAut.conj_apply]⟩
    · intro y hy
      apply (hmem H _).mp
      have hyq : π y ∈ K.map π := Subgroup.mem_map_of_mem π hy
      rw [← hq] at hyq
      obtain ⟨z, hz, he⟩ := hyq
      have he' : π g * z * (π g)⁻¹ = π y := he
      have hz' : π (g⁻¹ * y * (g⁻¹)⁻¹) = z := by
        simp only [map_mul, map_inv, inv_inv]
        rw [← he']
        group
      rwa [hz']



end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K : @Subgroup.{u_1} G inst)
  [inst_3 : @Subgroup.Normal.{u_1} G inst N]
  (hN :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) N))
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  (hquot :
    ∀ (U : @OpenNormalSubgroup.{u_1} G inst inst_1),
      @LocalConjugacy.Proof.LocalConjugacy.Conjugate.{u_1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
          (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
        (@QuotientGroup.Quotient.group.{u_1} G inst
          (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
          (@Subgroup.normal_inf_normal.{u_1} G inst N
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
            inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
        (@Subgroup.map.{u_1, u_1} G inst
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@Subgroup.normal_inf_normal.{u_1} G inst N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
              inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
          (@QuotientGroup.mk'.{u_1} G inst
            (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@Subgroup.normal_inf_normal.{u_1} G inst N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
              inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
          H)
        (@Subgroup.map.{u_1, u_1} G inst
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@Subgroup.normal_inf_normal.{u_1} G inst N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
              inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
          (@QuotientGroup.mk'.{u_1} G inst
            (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@Subgroup.normal_inf_normal.{u_1} G inst N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
              inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
          K)),
  @LocalConjugacy.Proof.LocalConjugacy.Conjugate.{u_1} G inst H K :=
  @LocalConjugacy.Proof.LocalConjugacy.conjugate_of_normal_intersection_quotients_preparedProof
