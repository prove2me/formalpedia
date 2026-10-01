-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.hasPrimes_singleton_iff_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:05:20.856017+00:00
-- url     : https://prove2.me/submissions/b6e38acd-3b43-4f7c-a149-a016c2d37d5d

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

private theorem hasPrimes_singleton_iff_isPGroup_preparedProof {G : Type*} [Group G] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] : HasPrimes {p} G ↔ IsPGroup p G := by
  constructor
  · intro h
    apply (isPGroup_iff_primeFactors_card_subset hp.out.ne_zero).mpr
    intro q hq
    obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    have he : q = p := h q hqprime hqdvd
    rw [he]
    exact Nat.mem_primeFactors.mpr ⟨hp.out, dvd_rfl, hp.out.ne_zero⟩
  · intro h q hq hd
    obtain ⟨k, hk⟩ := h.exists_card_eq
    rw [hk] at hd
    exact (Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow hd)



universe u





section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]









end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] {p : Nat} [hp : Fact (Nat.Prime p)],
  Iff
    (@LocalConjugacy.Proof.LocalConjugacy.HasPrimes.{u_1}
      (@Singleton.singleton.{0, 0} Nat (Set.{0} Nat) (@Set.instSingletonSet.{0} Nat) p) G inst)
    (@IsPGroup.{u_1} p G inst) :=
  @LocalConjugacy.Proof.LocalConjugacy.hasPrimes_singleton_iff_isPGroup_preparedProof
