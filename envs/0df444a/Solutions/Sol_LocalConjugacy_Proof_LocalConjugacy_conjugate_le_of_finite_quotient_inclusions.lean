-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.conjugate_le_of_finite_quotient_inclusions
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:28.404673+00:00
-- url     : https://prove2.me/submissions/55fc3e90-be47-4e24-9169-b84929f883b4

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



/-- The inclusion version of the compactness reduction. -/
private theorem conjugate_le_of_finite_quotient_inclusions_preparedProof (H K : Subgroup G)
    (hK : IsClosed (K : Set G))
    (hquot : ∀ U : OpenNormalSubgroup G, ∃ q : G ⧸ U.toSubgroup,
      conjugate q (H.map (QuotientGroup.mk' U.toSubgroup)) ≤
        K.map (QuotientGroup.mk' U.toSubgroup)) : ∃ g : G, conjugate g H ≤ K := by
  let : Nonempty (OpenNormalSubgroup G) := ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩
  let T : OpenNormalSubgroup G → Set G := fun U => transporter H (K ⊔ U.toSubgroup)
  have hc : ∀ U, IsClosed (T U) := fun U => transporter_closed _ _
    (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right U.isOpen))
  have hd : Directed (· ⊇ ·) T := by
    intro U V
    refine ⟨U ⊓ V, ?_, ?_⟩
    · intro g hg x hx
      exact (sup_le_sup_left inf_le_left K) (hg x hx)
    · intro g hg x hx
      exact (sup_le_sup_left inf_le_right K) (hg x hx)
  have hn : ∀ U, (T U).Nonempty := by
    intro U
    let π := QuotientGroup.mk' U.toSubgroup
    obtain ⟨q, hq⟩ := hquot U
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup q
    refine ⟨g, fun x hx => ?_⟩
    change (H.map π).map (MulAut.conj (π g)).toMonoidHom ≤ K.map π at hq
    have hm := hq (Subgroup.mem_map_of_mem (MulAut.conj (π g)).toMonoidHom
      (Subgroup.mem_map_of_mem π hx))
    change π g * π x * (π g)⁻¹ ∈ K.map π at hm
    have he : π (g * x * g⁻¹) ∈ K.map π := by
      simpa only [MulAut.conj_apply, map_mul, map_inv] using hm
    change g * x * g⁻¹ ∈ (K.map π).comap π at he
    simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using he
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hd hn (fun U => (hc U).isCompact) hc
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact mem_of_mem_sup_openNormal K hK _ (fun U => (Set.mem_iInter.mp hg U) x hx)

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (H K : @Subgroup.{u_1} G inst)
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  (hquot :
    ∀ (U : @OpenNormalSubgroup.{u_1} G inst inst_1),
      @Exists.{u_1 + 1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
        fun
          (q :
            @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
        @LE.le.{u_1}
          (@Subgroup.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u_1} G inst
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
          (@Preorder.toLE.{u_1}
            (@Subgroup.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            (@PartialOrder.toPreorder.{u_1}
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@Subgroup.instPartialOrder.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))))
          (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u_1} G inst
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
            q
            (@Subgroup.map.{u_1, u_1} G inst
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
              (@QuotientGroup.mk'.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
              H))
          (@Subgroup.map.{u_1, u_1} G inst
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u_1} G inst
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
            (@QuotientGroup.mk'.{u_1} G inst
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
            K)),
  @Exists.{u_1 + 1} G fun (g : G) =>
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g H) K :=
  @LocalConjugacy.Proof.LocalConjugacy.conjugate_le_of_finite_quotient_inclusions_preparedProof
