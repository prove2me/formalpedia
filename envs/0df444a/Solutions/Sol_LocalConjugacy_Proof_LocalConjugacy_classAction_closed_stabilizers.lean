-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.classAction_closed_stabilizers
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:38:59.01705+00:00
-- url     : https://prove2.me/submissions/53178b28-379b-4812-85e3-29663f44ba88

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

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





















private theorem classAction_closed_stabilizers_preparedProof [T2Space N]
    {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K)
    (Q : Subgroup J) (hinv : InvariantUnder Q K f) (g : CohomologyClass f) :
    @IsClosed Q _ (@MulAction.stabilizer Q (CohomologyClass f) _ (classAction f Q hinv) g : Set Q) := by
  letI := classAction f Q hinv
  have he : (MulAction.stabilizer Q g : Set Q) =
      ⋂ x : K, {q : Q | (q : J) • g.val.toFun (conjugateDomain K q x) = g.val.toFun x} := by
    ext q
    simp only [MulAction.mem_stabilizer_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h x
      exact congrArg (fun c : CohomologyClass f => c.val.toFun x) h
    · intro h
      apply Subtype.ext
      exact Cocycle.ext h
  rw [he]
  apply isClosed_iInter
  intro x
  apply isClosed_eq _ continuous_const
  apply Continuous.smul continuous_subtype_val
  apply g.val.continuous_toFun.comp
  exact ((continuous_subtype_val.inv.mul continuous_const).mul
    continuous_subtype_val).subtype_mk _



end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : @IsTopologicalGroup.{u_1} J inst_2 inst] [inst_4 : TopologicalSpace.{u_2} N]
  [inst_5 : @IsTopologicalGroup.{u_2} N inst_4 inst_1]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_7 :
    @ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  [@T2Space.{u_2} N inst_4] {K : @Subgroup.{u_1} J inst} [inst_9 : @Subgroup.Normal.{u_1} J inst K]
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K)
  (Q : @Subgroup.{u_1} J inst)
  (hinv : @LocalConjugacy.Proof.LocalConjugacy.InvariantUnder.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 Q K f)
  (g : @LocalConjugacy.Proof.LocalConjugacy.CohomologyClass.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K f),
  @IsClosed.{u_1}
    (@Subtype.{u_1 + 1} J fun (x : J) =>
      @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
    (@instTopologicalSpaceSubtype.{u_1} J
      (fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      inst_2)
    (@SetLike.coe.{u_1, u_1}
      (@Subgroup.{u_1}
        (@Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        (@Subgroup.toGroup.{u_1} J inst Q))
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.instSetLike.{u_1}
        (@Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        (@Subgroup.toGroup.{u_1} J inst Q))
      (@MulAction.stabilizer.{u_1, max u_2 u_1}
        (@Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        (@LocalConjugacy.Proof.LocalConjugacy.CohomologyClass.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K f)
        (@Subgroup.toGroup.{u_1} J inst Q)
        (@LocalConjugacy.Proof.LocalConjugacy.classAction.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6
          inst_7 K inst_9 f Q hinv)
        g)) :=
  @LocalConjugacy.Proof.LocalConjugacy.classAction_closed_stabilizers_preparedProof
