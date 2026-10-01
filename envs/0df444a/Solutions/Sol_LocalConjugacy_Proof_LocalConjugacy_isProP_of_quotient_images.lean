-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.isProP_of_quotient_images
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:24.709575+00:00
-- url     : https://prove2.me/submissions/a15b5481-c3de-4915-be2c-3ec1288c755b

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

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]



/-- Ambient open normal subgroups give a neighborhood basis in every subgroup. -/
private theorem exists_openNormal_le_subgroup_open (H : Subgroup G) (V : OpenNormalSubgroup H) :
    ∃ U : OpenNormalSubgroup G, ∀ x : H, (x : G) ∈ U → x ∈ V := by
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp V.isOpen
  have h1 : (1 : G) ∈ O := by
    have h : (1 : H) ∈ Subtype.val ⁻¹' O := by rw [hpre]; exact V.one_mem
    exact h
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  refine ⟨U, fun x hx => ?_⟩
  have h : x ∈ Subtype.val ⁻¹' O := hU hx
  rw [hpre] at h
  exact h

private theorem isProP_of_quotient_images_preparedProof {p : ℕ} (H : Subgroup G)
    (h : ∀ U : OpenNormalSubgroup G,
      IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup))) : IsProP p H := by
  intro V z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup z
  obtain ⟨U, hU⟩ := exists_openNormal_le_subgroup_open H V
  let π := QuotientGroup.mk' U.toSubgroup
  obtain ⟨k, hk⟩ := h U ⟨π x, Subgroup.mem_map_of_mem π x.property⟩
  refine ⟨k, ?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff (N := V.toSubgroup) _).mpr
  apply hU
  apply (QuotientGroup.eq_one_iff (N := U.toSubgroup) _).mp
  have he := congrArg Subtype.val hk
  simpa [π] using he





namespace FiniteSylowSystem
open CategoryTheory















variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)







include hP







end FiniteSylowSystem





























end LocalConjugacy

end LocalConjugacy.Proof

end

universe u

theorem solution :
∀ {G : Type u} [inst : Group.{u} G] [inst_1 : TopologicalSpace.{u} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u} G inst inst_1] {p : Nat} (H : @Subgroup.{u} G inst)
  (h :
    ∀ (U : @OpenNormalSubgroup.{u} G inst inst_1),
      @IsPGroup.{u} p
        (@Subtype.{u + 1}
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
          fun
            (x :
              @HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))) =>
          @Membership.mem.{u, u}
            (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
            (@Subgroup.{u}
              (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u} G inst
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
            (@SetLike.instMembership.{u, u}
              (@Subgroup.{u}
                (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                  (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u} G inst
                  (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
              (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
              (@Subgroup.instSetLike.{u}
                (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                  (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u} G inst
                  (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))))
            (@Subgroup.map.{u, u} G inst
              (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u} G inst
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
              (@QuotientGroup.mk'.{u} G inst
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
              H)
            x)
        (@Subgroup.toGroup.{u}
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
          (@Subgroup.map.{u, u} G inst
            (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
            (@QuotientGroup.mk'.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
            H))),
  @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u} p
    (@Subtype.{u + 1} G fun (x : G) =>
      @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
        (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
    (@Subgroup.toGroup.{u} G inst H)
    (@instTopologicalSpaceSubtype.{u} G
      (fun (x : G) =>
        @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
          (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
      inst_1) :=
  @LocalConjugacy.Proof.LocalConjugacy.isProP_of_quotient_images_preparedProof
