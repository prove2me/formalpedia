-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.subgroup_quotient_factors
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:02:02.713705+00:00
-- url     : https://prove2.me/submissions/c6852f07-e4bf-40eb-9df8-39f4153a48db

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

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Descent
variable {J F N : Type*} [Group J] [Group F] [Group N]
  [TopologicalSpace J] [TopologicalSpace F] [TopologicalSpace N]
  [MulDistribMulAction J N] [MulDistribMulAction F N]



private theorem subgroupImageHom_surjective (P : Subgroup J) (π : J →* F) :
    Function.Surjective (subgroupImageHom P π) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

namespace Cocycle


variable (P : Subgroup J) (π : J →* F)
  (ha : ∀ (j : J) (n : N), π j • n = j • n) (f : Cocycle (N := N) P)
  (hf : ∀ x y : P, π x = π y → f.toFun x = f.toFun y)











end Cocycle
end Descent

section OpenNormal
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N] [Finite N]





end OpenNormal
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy





universe u





section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- Every finite quotient of a subgroup factors through its image in an
ambient finite quotient. This also justifies inheritance of structural properties. -/
private theorem subgroup_quotient_factors_preparedProof (H : Subgroup G) (V : OpenNormalSubgroup H) :
    ∃ U : OpenNormalSubgroup G,
      ∃ f : H.map (QuotientGroup.mk' U.toSubgroup) →* H ⧸ V.toSubgroup,
        Function.Surjective f := by
  classical
  obtain ⟨U, hU⟩ := exists_openNormal_le_subgroup_open H V
  let φ := subgroupImageHom H (QuotientGroup.mk' U.toSubgroup)
  let ψ := QuotientGroup.mk' V.toSubgroup
  have hker : φ.ker ≤ ψ.ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff (N := V.toSubgroup) x).mpr
    apply hU
    apply (QuotientGroup.eq_one_iff (N := U.toSubgroup) (x : G)).mp
    exact congrArg Subtype.val hx
  let f := φ.liftOfSurjective (subgroupImageHom_surjective H _) ⟨ψ, hker⟩
  refine ⟨U, f, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup y
  exact ⟨φ x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩







end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (H : @Subgroup.{u_1} G inst)
  (V :
    @OpenNormalSubgroup.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
      (@Subgroup.toGroup.{u_1} G inst H)
      (@instTopologicalSpaceSubtype.{u_1} G
        (fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
        inst_1)),
  @Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} G inst inst_1) fun (U : @OpenNormalSubgroup.{u_1} G inst inst_1) =>
    @Exists.{u_1 + 1}
      (@MonoidHom.{u_1, u_1}
        (@Subtype.{u_1 + 1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
          fun
            (x :
              @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
          @Membership.mem.{u_1, u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@Subgroup.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.instSetLike.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
              H)
            x)
        (@HasQuotient.Quotient.{u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
          (@Subgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H))
          (@QuotientGroup.instHasQuotientSubgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H))
          (@OpenSubgroup.toSubgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H)
            (@instTopologicalSpaceSubtype.{u_1} G
              (fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              inst_1)
            (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H)
              (@instTopologicalSpaceSubtype.{u_1} G
                (fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                inst_1)
              V)))
        (@MulOneClass.toMulOne.{u_1}
          (@Subtype.{u_1 + 1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            fun
              (x :
                @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
            @Membership.mem.{u_1, u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.instSetLike.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                H)
              x)
          (@Monoid.toMulOneClass.{u_1}
            (@Subtype.{u_1 + 1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              fun
                (x :
                  @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
              @Membership.mem.{u_1, u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.instSetLike.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                  H)
                x)
            (@DivInvMonoid.toMonoid.{u_1}
              (@Subtype.{u_1 + 1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                fun
                  (x :
                    @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                @Membership.mem.{u_1, u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.instSetLike.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                    H)
                  x)
              (@Group.toDivInvMonoid.{u_1}
                (@Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                      H)
                    x)
                (@Subgroup.toGroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
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
                    H))))))
        (@MulOneClass.toMulOne.{u_1}
          (@HasQuotient.Quotient.{u_1, u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H))
            (@QuotientGroup.instHasQuotientSubgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H))
            (@OpenSubgroup.toSubgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H)
              (@instTopologicalSpaceSubtype.{u_1} G
                (fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                inst_1)
              (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                V)))
          (@Monoid.toMulOneClass.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
            (@DivInvMonoid.toMonoid.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@OpenSubgroup.toSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))
              (@Group.toDivInvMonoid.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V)))
                (@QuotientGroup.Quotient.group.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V))
                  (@OpenNormalSubgroup.instNormal.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))))))
      fun
        (f :
          @MonoidHom.{u_1, u_1}
            (@Subtype.{u_1 + 1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              fun
                (x :
                  @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
              @Membership.mem.{u_1, u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.instSetLike.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                  H)
                x)
            (@HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
            (@MulOneClass.toMulOne.{u_1}
              (@Subtype.{u_1 + 1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                fun
                  (x :
                    @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                @Membership.mem.{u_1, u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.instSetLike.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                    H)
                  x)
              (@Monoid.toMulOneClass.{u_1}
                (@Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                      H)
                    x)
                (@DivInvMonoid.toMonoid.{u_1}
                  (@Subtype.{u_1 + 1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    fun
                      (x :
                        @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                    @Membership.mem.{u_1, u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@SetLike.instMembership.{u_1, u_1}
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.instSetLike.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                        H)
                      x)
                  (@Group.toDivInvMonoid.{u_1}
                    (@Subtype.{u_1 + 1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      fun
                        (x :
                          @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                      @Membership.mem.{u_1, u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@SetLike.instMembership.{u_1, u_1}
                          (@Subgroup.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@Subgroup.instSetLike.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                          H)
                        x)
                    (@Subgroup.toGroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
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
                        H))))))
            (@MulOneClass.toMulOne.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@OpenSubgroup.toSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))
              (@Monoid.toMulOneClass.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V)))
                (@DivInvMonoid.toMonoid.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@OpenSubgroup.toSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))
                  (@Group.toDivInvMonoid.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V)))
                    (@QuotientGroup.Quotient.group.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V))
                      (@OpenNormalSubgroup.instNormal.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V))))))) =>
      @Function.Surjective.{u_1 + 1, u_1 + 1}
        (@Subtype.{u_1 + 1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
          fun
            (x :
              @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
          @Membership.mem.{u_1, u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@Subgroup.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.instSetLike.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
              H)
            x)
        (@HasQuotient.Quotient.{u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
          (@Subgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H))
          (@QuotientGroup.instHasQuotientSubgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H))
          (@OpenSubgroup.toSubgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H)
            (@instTopologicalSpaceSubtype.{u_1} G
              (fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              inst_1)
            (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H)
              (@instTopologicalSpaceSubtype.{u_1} G
                (fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                inst_1)
              V)))
        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
          (@MonoidHom.{u_1, u_1}
            (@Subtype.{u_1 + 1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              fun
                (x :
                  @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
              @Membership.mem.{u_1, u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.instSetLike.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                  H)
                x)
            (@HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
            (@MulOneClass.toMulOne.{u_1}
              (@Subtype.{u_1 + 1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                fun
                  (x :
                    @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                @Membership.mem.{u_1, u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.instSetLike.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                    H)
                  x)
              (@Monoid.toMulOneClass.{u_1}
                (@Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                      H)
                    x)
                (@DivInvMonoid.toMonoid.{u_1}
                  (@Subtype.{u_1 + 1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    fun
                      (x :
                        @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                    @Membership.mem.{u_1, u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@SetLike.instMembership.{u_1, u_1}
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.instSetLike.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                        H)
                      x)
                  (@Group.toDivInvMonoid.{u_1}
                    (@Subtype.{u_1 + 1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      fun
                        (x :
                          @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                      @Membership.mem.{u_1, u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@SetLike.instMembership.{u_1, u_1}
                          (@Subgroup.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@Subgroup.instSetLike.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                          H)
                        x)
                    (@Subgroup.toGroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
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
                        H))))))
            (@MulOneClass.toMulOne.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@OpenSubgroup.toSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))
              (@Monoid.toMulOneClass.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V)))
                (@DivInvMonoid.toMonoid.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@OpenSubgroup.toSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))
                  (@Group.toDivInvMonoid.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V)))
                    (@QuotientGroup.Quotient.group.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V))
                      (@OpenNormalSubgroup.instNormal.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))))))
          (@Subtype.{u_1 + 1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            fun
              (x :
                @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
            @Membership.mem.{u_1, u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.instSetLike.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                H)
              x)
          (fun
              (x :
                @Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                      H)
                    x) =>
            @HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
          (@MonoidHom.instFunLike.{u_1, u_1}
            (@Subtype.{u_1 + 1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              fun
                (x :
                  @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
              @Membership.mem.{u_1, u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.instSetLike.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                  H)
                x)
            (@HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
            (@MulOneClass.toMulOne.{u_1}
              (@Subtype.{u_1 + 1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                fun
                  (x :
                    @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                @Membership.mem.{u_1, u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.instSetLike.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                    H)
                  x)
              (@Monoid.toMulOneClass.{u_1}
                (@Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                      H)
                    x)
                (@DivInvMonoid.toMonoid.{u_1}
                  (@Subtype.{u_1 + 1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    fun
                      (x :
                        @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                    @Membership.mem.{u_1, u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@SetLike.instMembership.{u_1, u_1}
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.instSetLike.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                        H)
                      x)
                  (@Group.toDivInvMonoid.{u_1}
                    (@Subtype.{u_1 + 1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      fun
                        (x :
                          @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                      @Membership.mem.{u_1, u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@SetLike.instMembership.{u_1, u_1}
                          (@Subgroup.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@Subgroup.instSetLike.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
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
                          H)
                        x)
                    (@Subgroup.toGroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
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
                        H))))))
            (@MulOneClass.toMulOne.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@OpenSubgroup.toSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))
              (@Monoid.toMulOneClass.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V)))
                (@DivInvMonoid.toMonoid.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@OpenSubgroup.toSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))
                  (@Group.toDivInvMonoid.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V)))
                    (@QuotientGroup.Quotient.group.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V))
                      (@OpenNormalSubgroup.instNormal.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))))))
          f) :=
  @LocalConjugacy.Proof.LocalConjugacy.subgroup_quotient_factors_preparedProof
