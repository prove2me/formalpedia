-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.cohomologous_trivial_of_coprime_proP
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:49:44.248201+00:00
-- url     : https://prove2.me/submissions/cd09999f-fae6-40dc-a471-5b3e10870235

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_proP_fixed_point

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N]



/-- The coprime vanishing fact used in the finite-coefficient case of
Proposition 2.2 and Lemma 1.2. The acting pro-`q` group may be infinite. -/
private theorem cohomologous_trivial_of_coprime_proP_preparedProof
    [IsTopologicalGroup J] [IsTopologicalGroup N] [DiscreteTopology N]
    [ContinuousSMul J N] [Finite N] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hne : q ≠ p) (hN : IsPGroup p N) (K : Subgroup J) (hK : IsProP q K)
    (f : Cocycle (N := N) K) : Cohomologous f (trivialCocycle K) := by
  letI := cocycleAffineAction f
  have hc (n : N) : IsClosed (MulAction.stabilizer K n : Set K) := by
    change IsClosed {x : K | f.toFun x * ((x : J) • n) = n}
    exact isClosed_eq (f.continuous_toFun.mul
      (continuous_subtype_val.smul continuous_const)) continuous_const
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have hn : ¬ q ∣ Nat.card N := by
    rw [hk]
    exact fun h => hne ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
      (Fact.out : p.Prime)).mp ((Fact.out : q.Prime).dvd_of_dvd_pow h))
  obtain ⟨n, hn⟩ := proP_fixed_point hK hc hn
  refine ⟨n, fun x => ?_⟩
  change 1 = n⁻¹ * f.toFun x * ((x : J) • n)
  have he : f.toFun x * ((x : J) • n) = n := hn x
  rw [mul_assoc, he, inv_mul_cancel]

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : TopologicalSpace.{u_2} N]
  [inst_4 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@IsTopologicalGroup.{u_1} J inst_2 inst] [@IsTopologicalGroup.{u_2} N inst_3 inst_1]
  [@DiscreteTopology.{u_2} N inst_3]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4)))
      inst_2 inst_3]
  [Finite.{u_2 + 1} N] {p q : Nat} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (hne : @Ne.{1} Nat q p)
  (hN : @IsPGroup.{u_2} p N inst_1) (K : @Subgroup.{u_1} J inst)
  (hK :
    @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u_1} q
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K x)
      (@Subgroup.toGroup.{u_1} J inst K)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K x)
        inst_2))
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 K),
  @LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 K f
    (@LocalConjugacy.Proof.LocalConjugacy.trivialCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 K) :=
  @LocalConjugacy.Proof.LocalConjugacy.cohomologous_trivial_of_coprime_proP_preparedProof
