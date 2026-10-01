-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.exists_cocycle_neighborhood_kernel
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:53:38.153389+00:00
-- url     : https://prove2.me/submissions/8db6ee74-682d-4f5f-acae-f587e06c11a3

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
open scoped Pointwise

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- A small open normal subgroup kills a cocycle on its domain and fixes its
finite image. The coefficient group itself may be infinite. -/
private theorem exists_cocycle_neighborhood_kernel_preparedProof (H : Subgroup J)
    (hH : IsClosed (H : Set J)) (f : Cocycle (N := N) H) :
    ∃ U : OpenNormalSubgroup J,
      (∀ u ∈ U, ∀ x : H, u • f.toFun x = f.toFun x) ∧
      ∀ x : H, (x : J) ∈ U → f.toFun x = 1 := by
  letI := profinite_closed_subgroup H hH
  have hf : (Set.range f.toFun).Finite :=
    (isCompact_range f.continuous_toFun).finite_of_discrete
  let A : Set J := ⋂ n ∈ Set.range f.toFun, {j : J | j • n = n}
  have hA : IsOpen A := hf.isOpen_biInter fun n _ =>
    (continuous_id.smul continuous_const).isOpen_preimage _ (isOpen_discrete {n})
  have h1A : (1 : J) ∈ A := by simp [A]
  have ho : IsOpen (f.toFun ⁻¹' {1}) :=
    f.continuous_toFun.isOpen_preimage _ (isOpen_discrete _)
  obtain ⟨O, hO, he⟩ := isOpen_induced_iff.mp ho
  have h1O : (1 : J) ∈ O := by
    have hh : (1 : H) ∈ Subtype.val ⁻¹' O := by rw [he]; exact cocycle_one f
    exact hh
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hA.inter hO) ⟨h1A, h1O⟩
  refine ⟨U, ?_, ?_⟩
  · intro u hu x
    exact Set.mem_iInter.mp (Set.mem_iInter.mp (hU hu).1 (f.toFun x)) ⟨x, rfl⟩
  · intro x hx
    have hh : x ∈ Subtype.val ⁻¹' O := (hU hx).2
    rw [he] at hh
    exact hh



end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  (H : @Subgroup.{u_1} J inst)
  (hH :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H),
  @Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} J inst inst_2) fun (U : @OpenNormalSubgroup.{u_1} J inst inst_2) =>
    And
      (∀ (u : J),
        @Membership.mem.{u_1, u_1} J (@OpenNormalSubgroup.{u_1} J inst inst_2)
            (@SetLike.instMembership.{u_1, u_1} (@OpenNormalSubgroup.{u_1} J inst inst_2) J
              (@OpenNormalSubgroup.instSetLike.{u_1} J inst inst_2))
            U u →
          ∀
            (x :
              @Subtype.{u_1 + 1} J fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) H
                  x),
            @Eq.{u_2 + 1} N
              (@HSMul.hSMul.{u_1, u_2, u_2} J N N
                (@instHSMul.{u_1, u_2} J N
                  (@SemigroupAction.toSMul.{u_1, u_2} J N
                    (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
                    (@MulAction.toSemigroupAction.{u_1, u_2} J N
                      (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                      (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                        (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                        (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6))))
                u (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H f x))
              (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H f x))
      (∀
        (x :
          @Subtype.{u_1 + 1} J fun (x : J) =>
            @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) H x),
        @Membership.mem.{u_1, u_1} J (@OpenNormalSubgroup.{u_1} J inst inst_2)
            (@SetLike.instMembership.{u_1, u_1} (@OpenNormalSubgroup.{u_1} J inst inst_2) J
              (@OpenNormalSubgroup.instSetLike.{u_1} J inst inst_2))
            U
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) H
                  x)
              x) →
          @Eq.{u_2 + 1} N (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H f x)
            (@OfNat.ofNat.{u_2} N (nat_lit 1)
              (@One.toOfNat1.{u_2} N
                (@InvOneClass.toOne.{u_2} N
                  (@DivInvOneMonoid.toInvOneClass.{u_2} N
                    (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1))))))) :=
  @LocalConjugacy.Proof.LocalConjugacy.exists_cocycle_neighborhood_kernel_preparedProof
