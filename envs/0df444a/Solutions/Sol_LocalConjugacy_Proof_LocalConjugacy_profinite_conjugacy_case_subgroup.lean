-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.profinite_conjugacy_case_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:26:17.468885+00:00
-- url     : https://prove2.me/submissions/125cf657-d3fc-436a-80cd-6551c631d87c

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_profinite_quotient
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

/-- A continuous discrete quotient of a pronilpotent group is nilpotent. -/
private theorem nilpotent_of_pronilpotent_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Group.IsNilpotent F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  letI := hG U
  exact Group.nilpotent_of_surjective (QuotientGroup.kerLift f)
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

/-! The pronilpotent branch of Lemma 1.2, using the manuscript's two Zorn
arguments: first a fixed pair of cocycles, then one stable class. -/

namespace LocalConjugacy

private theorem pronilpotent_subgroup {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]
    (hJ : Pronilpotent J) (L : Subgroup J) : Pronilpotent L := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors L V
  letI := hJ U
  exact Group.nilpotent_of_surjective f hf



variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





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



private theorem pronilpotent_of_continuous_injective (hG : Pronilpotent G)
    (f : F →* G) (hf : Continuous f) (hi : Function.Injective f) : Pronilpotent F := by
  let e : F ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y he => hi (congrArg Subtype.val he), f.rangeRestrict_surjective⟩
  have he : Continuous e := hf.subtype_mk _
  have hei : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  intro V
  exact nilpotent_of_pronilpotent_surjective (pronilpotent_subgroup hG f.range)
    ((QuotientGroup.mk' V.toSubgroup).comp e.symm.toMonoidHom)
    (continuous_quotient_mk'.comp hei)
    ((QuotientGroup.mk'_surjective V.toSubgroup).comp e.symm.surjective)



end Topology

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]



private theorem profinite_conjugacy_case_subgroup_preparedProof (N L : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hL : IsClosed (L : Set G))
    (h : Prosupersolvable G ∨ Pronilpotent (G ⧸ N)) :
    Prosupersolvable L ∨ Pronilpotent (L ⧸ N.subgroupOf L) := by
  rcases h with h | h
  · exact Or.inl (prosupersolvable_subgroup h L)
  · letI := profinite_closed_subgroup L hL
    letI := profinite_quotient N hN
    letI := profinite_quotient (N.subgroupOf L) (hN.preimage continuous_subtype_val)
    let f := (QuotientGroup.mk' N).comp L.subtype
    let φ := QuotientGroup.lift (N.subgroupOf L) f (by
      intro x hx
      exact (QuotientGroup.eq_one_iff (x : G)).mpr hx)
    apply Or.inr
    apply pronilpotent_of_continuous_injective h φ
    · exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (continuous_quotient_mk'.comp continuous_subtype_val)
    · intro x y
      induction x using QuotientGroup.induction_on with | H x =>
        induction y using QuotientGroup.induction_on with | H y =>
          intro he
          change QuotientGroup.mk' N (x : G) = QuotientGroup.mk' N (y : G) at he
          have hm : (x : G)⁻¹ * (y : G) ∈ N := QuotientGroup.eq.mp he
          exact QuotientGroup.eq.mpr hm





end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N L : @Subgroup.{u_1} G inst)
  [inst_3 : @Subgroup.Normal.{u_1} G inst N]
  (hN :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) N))
  (hL :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) L))
  (h :
    Or (@LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1} G inst inst_1)
      (@LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
        (@QuotientGroup.Quotient.group.{u_1} G inst N inst_3)
        (@QuotientGroup.instTopologicalSpace.{u_1} G inst_1 inst N))),
  Or
    (@LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
      (@Subgroup.toGroup.{u_1} G inst L)
      (@instTopologicalSpaceSubtype.{u_1} G
        (fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
        inst_1))
    (@LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1}
      (@HasQuotient.Quotient.{u_1, u_1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
        (@Subgroup.{u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
          (@Subgroup.toGroup.{u_1} G inst L))
        (@QuotientGroup.instHasQuotientSubgroup.{u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
          (@Subgroup.toGroup.{u_1} G inst L))
        (@Subgroup.subgroupOf.{u_1} G inst N L))
      (@QuotientGroup.Quotient.group.{u_1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
        (@Subgroup.toGroup.{u_1} G inst L) (@Subgroup.subgroupOf.{u_1} G inst N L)
        (@Subgroup.normal_subgroupOf.{u_1} G inst L N inst_3))
      (@QuotientGroup.instTopologicalSpace.{u_1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
        (@instTopologicalSpaceSubtype.{u_1} G
          (fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) L x)
          inst_1)
        (@Subgroup.toGroup.{u_1} G inst L) (@Subgroup.subgroupOf.{u_1} G inst N L))) :=
  @LocalConjugacy.Proof.LocalConjugacy.profinite_conjugacy_case_subgroup_preparedProof
