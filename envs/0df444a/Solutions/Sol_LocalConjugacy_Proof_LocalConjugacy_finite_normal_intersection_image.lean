-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.finite_normal_intersection_image
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:13:02.787916+00:00
-- url     : https://prove2.me/submissions/949abdee-169a-4771-a7ed-ac1c9bba82b6

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

/-! The precise compactness system in Theorem 1.1: the quotients are by
`N ∩ U`, and their normal subgroups have finite order, although the quotients
themselves need not be finite. -/

namespace LocalConjugacy
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

private theorem finite_normal_intersection_image_preparedProof (N : Subgroup G) [N.Normal]
    (U : OpenNormalSubgroup G) :
    Finite (N.map (QuotientGroup.mk' (N ⊓ U.toSubgroup))) := by
  let D := N ⊓ U.toSubgroup
  let π := QuotientGroup.mk' D
  let ρ : G ⧸ D →* G ⧸ U.toSubgroup :=
    QuotientGroup.map D U.toSubgroup (MonoidHom.id G) inf_le_right
  let f : N.map π → G ⧸ U.toSubgroup := fun x => ρ x
  apply Finite.of_injective f
  rintro ⟨_, n, hn, rfl⟩ ⟨_, m, hm, rfl⟩ he
  apply Subtype.ext
  apply QuotientGroup.eq.mpr
  change QuotientGroup.mk' U.toSubgroup n = QuotientGroup.mk' U.toSubgroup m at he
  exact ⟨N.mul_mem (N.inv_mem hn) hm, QuotientGroup.eq.mp he⟩





end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N : @Subgroup.{u_1} G inst)
  [inst_3 : @Subgroup.Normal.{u_1} G inst N] (U : @OpenNormalSubgroup.{u_1} G inst inst_1),
  Finite.{u_1 + 1}
    (@Subtype.{u_1 + 1}
      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
        (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
      fun
        (x :
          @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))) =>
      @Membership.mem.{u_1, u_1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
          (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
        (@Subgroup.{u_1}
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
              inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
        (@SetLike.instMembership.{u_1, u_1}
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
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))))
          (@Subgroup.instSetLike.{u_1}
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
                inst_3 (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))))
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
          N)
        x) :=
  @LocalConjugacy.Proof.LocalConjugacy.finite_normal_intersection_image_preparedProof
