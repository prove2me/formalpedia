-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.exists_finite_invariant_coefficient_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:51:41.778995+00:00
-- url     : https://prove2.me/submissions/7c29f5b8-511a-47ea-924b-1887d6b7c040

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



section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [CompactSpace J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- A finite set of coefficients is contained in a finite invariant subgroup.
Compactness makes each orbit finite; local finiteness handles their generated subgroup. -/
private theorem exists_finite_invariant_coefficient_subgroup_preparedProof (hN : LocallyFiniteGroup N)
    (s : Set N) (hs : s.Finite) :
    ∃ M : Subgroup N, Finite M ∧ s ⊆ M ∧
      ∀ (j : J) (n : N), n ∈ M → j • n ∈ M := by
  let t : Set N := ⋃ n ∈ s, Set.range (fun j : J => j • n)
  have ht : t.Finite := hs.biUnion fun n _ =>
    (isCompact_range (continuous_id.smul continuous_const)).finite_of_discrete
  let M := Subgroup.closure t
  refine ⟨M, (hN t ht).to_subtype, ?_, ?_⟩
  · intro n hn
    apply Subgroup.subset_closure
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn, ⟨1, one_smul J n⟩⟩⟩
  · intro j n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
        obtain ⟨has, k, rfl⟩ := Set.mem_iUnion.mp ha
        apply Subgroup.subset_closure
        exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨has,
          ⟨j * k, mul_smul j k a⟩⟩⟩
    | one => simpa only [smul_one] using M.one_mem
    | mul x y _ _ hx hy => simpa only [smul_mul'] using M.mul_mem hx hy
    | inv x _ hx => simpa only [smul_inv'] using M.inv_mem hx

end

section Subgroup
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N]
  [MulDistribMulAction J N]
  (M : Subgroup N) (hM : ∀ (j : J) (n : N), n ∈ M → j • n ∈ M)





namespace Cocycle



end Cocycle
end Subgroup

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@CompactSpace.{u_1} J inst_2] [inst_4 : TopologicalSpace.{u_2} N] [@DiscreteTopology.{u_2} N inst_4]
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
  (hN : @LocalConjugacy.Proof.LocalConjugacy.LocallyFiniteGroup.{u_2} N inst_1) (s : Set.{u_2} N)
  (hs : @Set.Finite.{u_2} N s),
  @Exists.{u_2 + 1} (@Subgroup.{u_2} N inst_1) fun (M : @Subgroup.{u_2} N inst_1) =>
    And
      (Finite.{u_2 + 1}
        (@Subtype.{u_2 + 1} N fun (x : N) =>
          @Membership.mem.{u_2, u_2} N (@Subgroup.{u_2} N inst_1)
            (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} N inst_1) N (@Subgroup.instSetLike.{u_2} N inst_1)) M
            x))
      (And
        (@LE.le.{u_2} (Set.{u_2} N) (@Set.instLE.{u_2} N) s
          (@SetLike.coe.{u_2, u_2} (@Subgroup.{u_2} N inst_1) N (@Subgroup.instSetLike.{u_2} N inst_1) M))
        (∀ (j : J) (n : N),
          @Membership.mem.{u_2, u_2} N (@Subgroup.{u_2} N inst_1)
              (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} N inst_1) N (@Subgroup.instSetLike.{u_2} N inst_1)) M
              n →
            @Membership.mem.{u_2, u_2} N (@Subgroup.{u_2} N inst_1)
              (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} N inst_1) N (@Subgroup.instSetLike.{u_2} N inst_1)) M
              (@HSMul.hSMul.{u_1, u_2, u_2} J N N
                (@instHSMul.{u_1, u_2} J N
                  (@SemigroupAction.toSMul.{u_1, u_2} J N
                    (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
                    (@MulAction.toSemigroupAction.{u_1, u_2} J N
                      (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                      (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                        (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                        (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6))))
                j n))) :=
  @LocalConjugacy.Proof.LocalConjugacy.exists_finite_invariant_coefficient_subgroup_preparedProof
