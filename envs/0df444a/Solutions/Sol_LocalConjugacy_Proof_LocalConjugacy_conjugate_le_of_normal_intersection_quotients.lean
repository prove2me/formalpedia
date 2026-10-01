-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.conjugate_le_of_normal_intersection_quotients
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:45:16.739764+00:00
-- url     : https://prove2.me/submissions/6c940b8e-f84e-461a-b95d-9457da6a4310

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



end LocalConjugacy

end LocalConjugacy.Proof

end

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

/-! Proposition 4.1 in the order of the manuscript: induction for finite `N`,
then compactness in the quotients by `N ∩ U`. -/

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- The inclusion form of the manuscript's normal-intersection compactness
argument. The quotients need not be finite. -/
private theorem conjugate_le_of_normal_intersection_quotients_preparedProof
    (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hquot : ∀ U : OpenNormalSubgroup G, ∃ q : G ⧸ (N ⊓ U.toSubgroup),
      conjugate q (K.map (QuotientGroup.mk' (N ⊓ U.toSubgroup))) ≤
        H.map (QuotientGroup.mk' (N ⊓ U.toSubgroup))) :
    ∃ g : G, conjugate g K ≤ H := by
  let : Nonempty (OpenNormalSubgroup G) := ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩
  let T : OpenNormalSubgroup G → Set G := fun U => transporter K (H ⊔ (N ⊓ U.toSubgroup))
  have hc : ∀ U, IsClosed (T U) := by
    intro U
    apply transporter_closed
    rw [sup_comm]
    exact closed_sup_normal _ H (hN.inter U.isClosed) hH
  have hd : Directed (· ⊇ ·) T := by
    intro U V
    refine ⟨U ⊓ V, ?_, ?_⟩
    · intro g hg x hx
      exact (sup_le_sup_left (inf_le_inf_left N inf_le_left) H) (hg x hx)
    · intro g hg x hx
      exact (sup_le_sup_left (inf_le_inf_left N inf_le_right) H) (hg x hx)
  have hn : ∀ U, (T U).Nonempty := by
    intro U
    let D := N ⊓ U.toSubgroup
    let π := QuotientGroup.mk' D
    obtain ⟨q, hq⟩ := hquot U
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
    refine ⟨g, fun x hx => ?_⟩
    change (K.map π).map (MulAut.conj (π g)).toMonoidHom ≤ H.map π at hq
    have hm := hq (Subgroup.mem_map_of_mem (MulAut.conj (π g)).toMonoidHom
      (Subgroup.mem_map_of_mem π hx))
    change π g * π x * (π g)⁻¹ ∈ H.map π at hm
    have he : π (g * x * g⁻¹) ∈ H.map π := by
      simpa only [MulAut.conj_apply, map_mul, map_inv] using hm
    change g * x * g⁻¹ ∈ (H.map π).comap π at he
    simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using he
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hd hn (fun U => (hc U).isCompact) hc
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact mem_of_mem_sup_openNormal H hH _ (fun U =>
    (sup_le_sup_left inf_le_right H) ((Set.mem_iInter.mp hg U) x hx))



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
  (hquot :
    ∀ (U : @OpenNormalSubgroup.{u_1} G inst inst_1),
      @Exists.{u_1 + 1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
          (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
        fun
          (q :
            @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))) =>
        @LE.le.{u_1}
          (@Subgroup.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
            (@QuotientGroup.Quotient.group.{u_1} G inst
              (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.normal_inf_normal.{u_1} G inst N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
          (@Preorder.toLE.{u_1}
            (@Subgroup.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.normal_inf_normal.{u_1} G inst N
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
            (@PartialOrder.toPreorder.{u_1}
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.normal_inf_normal.{u_1} G inst N
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
              (@Subgroup.instPartialOrder.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.normal_inf_normal.{u_1} G inst N
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))))
          (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
            (@QuotientGroup.Quotient.group.{u_1} G inst
              (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.normal_inf_normal.{u_1} G inst N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            q
            (@Subgroup.map.{u_1, u_1} G inst
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.normal_inf_normal.{u_1} G inst N
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@QuotientGroup.mk'.{u_1} G inst
                (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.normal_inf_normal.{u_1} G inst N
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              K))
          (@Subgroup.map.{u_1, u_1} G inst
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
            (@QuotientGroup.Quotient.group.{u_1} G inst
              (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.normal_inf_normal.{u_1} G inst N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            (@QuotientGroup.mk'.{u_1} G inst
              (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.normal_inf_normal.{u_1} G inst N
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            H)),
  @Exists.{u_1 + 1} G fun (g : G) =>
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g K) H :=
  @LocalConjugacy.Proof.LocalConjugacy.conjugate_le_of_normal_intersection_quotients_preparedProof
