-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.prosupersolvable_restricted_action
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:11:59.093985+00:00
-- url     : https://prove2.me/submissions/3fed7fbd-41d6-4dd5-ba63-18281b95c260

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_subgroup_quotient_factors
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supersolvable_subgroup

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]





end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]



/-- A continuous discrete quotient of a prosupersolvable group is
supersolvable, with the actual normal cyclic series transported. -/
private theorem supersolvable_of_prosupersolvable_surjective (hG : Prosupersolvable G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Supersolvable F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  exact supersolvable_of_surjective (hG U) (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)



end Topology

section Discrete
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]





end Discrete
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy





universe u





section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]



/-- Closed subgroups of prosupersolvable groups are prosupersolvable.
The algebraic conclusion even holds for the induced topology on any subgroup. -/
private theorem prosupersolvable_subgroup (hG : Prosupersolvable G) (H : Subgroup G) :
    Prosupersolvable H := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors H V
  exact supersolvable_of_surjective (supersolvable_subgroup (hG U) _) f hf





end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

private theorem prosupersolvable_of_continuous_injective {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [Profinite G] [TopologicalSpace H] [Profinite H]
    (hG : Prosupersolvable G) (f : H →* G) (hf : Continuous f) (hi : Function.Injective f) :
    Prosupersolvable H := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y he => hi (congrArg Subtype.val he), f.rangeRestrict_surjective⟩
  have he : Continuous e := hf.subtype_mk _
  have hei : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  intro V
  exact supersolvable_of_prosupersolvable_surjective (prosupersolvable_subgroup hG f.range)
    ((QuotientGroup.mk' V.toSubgroup).comp e.symm.toMonoidHom)
    (continuous_quotient_mk'.comp hei)
    ((QuotientGroup.mk'_surjective V.toSubgroup).comp e.symm.surjective)

section Action
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

private theorem prosupersolvable_restricted_action_preparedProof (hG : Prosupersolvable (ActionProduct J N))
    (L : Subgroup J) (hL : IsClosed (L : Set J)) : Prosupersolvable (ActionProduct L N) := by
  letI := profinite_closed_subgroup L hL
  let f : ActionProduct L N →* ActionProduct J N :=
    SemidirectProduct.map (MonoidHom.id N) L.subtype (fun _ => rfl)
  apply prosupersolvable_of_continuous_injective hG f
  · apply continuous_induced_rng.mpr
    exact actionProduct_continuous_left.prodMk
      (continuous_subtype_val.comp actionProduct_continuous_right)
  · intro x y he
    apply SemidirectProduct.ext
    · exact congrArg (fun z : ActionProduct J N => z.left) he
    · exact Subtype.ext (congrArg (fun z : ActionProduct J N => z.right) he)



end Action
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4] [Finite.{u_2 + 1} N]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  (hG :
    @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{max u_2 u_1}
      (@LocalConjugacy.Proof.LocalConjugacy.ActionProduct.{u_1, u_2} J N inst inst_1 inst_7)
      (@SemidirectProduct.instGroup.{u_2, u_1} N J inst_1 inst
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7))
      (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u_1, u_2} J N inst inst_1 inst_2 inst_4
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
  (L : @Subgroup.{u_1} J inst)
  (hL :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) L)),
  @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{max u_2 u_1}
    (@LocalConjugacy.Proof.LocalConjugacy.ActionProduct.{u_1, u_2}
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) L x)
      N (@Subgroup.toGroup.{u_1} J inst L) inst_1
      (@Subgroup.instMulDistribMulActionSubtypeMem.{u_1, u_2} J N inst
        (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7 L))
    (@SemidirectProduct.instGroup.{u_2, u_1} N
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) L x)
      inst_1 (@Subgroup.toGroup.{u_1} J inst L)
      (@MulDistribMulAction.toMulAut.{u_1, u_2}
        (@Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) L x)
        N (@Subgroup.toGroup.{u_1} J inst L) (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))
        (@Subgroup.instMulDistribMulActionSubtypeMem.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7 L)))
    (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u_1, u_2}
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) L x)
      N (@Subgroup.toGroup.{u_1} J inst L) inst_1
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) L x)
        inst_2)
      inst_4
      (@MulDistribMulAction.toMulAut.{u_1, u_2}
        (@Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) L x)
        N (@Subgroup.toGroup.{u_1} J inst L) (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))
        (@Subgroup.instMulDistribMulActionSubtypeMem.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7 L))) :=
  @LocalConjugacy.Proof.LocalConjugacy.prosupersolvable_restricted_action_preparedProof
