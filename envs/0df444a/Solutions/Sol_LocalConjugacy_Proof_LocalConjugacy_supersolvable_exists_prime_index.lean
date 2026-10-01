-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.supersolvable_exists_prime_index
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:09:31.441764+00:00
-- url     : https://prove2.me/submissions/c25731b0-d05c-49ae-8c07-74cf88e383d9

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

/-- A nontrivial finite supersolvable group has a normal subgroup of prime index. -/
private theorem supersolvable_exists_prime_index_preparedProof {G : Type u} [Group G] [Finite G]
    [Nontrivial G] (hG : Supersolvable G) :
    ∃ K : Subgroup G, K.Normal ∧ K.index.Prime := by
  suffices h : ∀ k : ℕ, ∀ {G : Type u} [Group G] [Finite G] [Nontrivial G],
      Nat.card G = k → Supersolvable G → ∃ K : Subgroup G, K.Normal ∧ K.index.Prime by
    exact h (Nat.card G) rfl hG
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G _ _ _ hcard hG
    obtain ⟨C, q, hCn, hq, hCcard⟩ := supersolvable_exists_prime_normal hG
    letI := hCn
    by_cases hC : C = ⊤
    · refine ⟨⊥, inferInstance, ?_⟩
      rw [hC, Subgroup.card_top] at hCcard
      simpa only [Subgroup.index_bot, hCcard] using hq
    · letI : Nontrivial (G ⧸ C) := QuotientGroup.nontrivial_iff.mpr hC
      have hquot : Nat.card (G ⧸ C) < k := by
        have hc := C.card_mul_index
        change Nat.card C * Nat.card (G ⧸ C) = Nat.card G at hc
        rw [hCcard, hcard] at hc
        have hpos := Nat.card_pos (α := G ⧸ C)
        have hq2 := hq.two_le
        nlinarith
      obtain ⟨K, hKn, hK⟩ := ih _ hquot rfl (supersolvable_of_surjective hG
        (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C))
      letI := hKn
      refine ⟨K.comap (QuotientGroup.mk' C), inferInstance, ?_⟩
      rwa [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective C)]



section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]









end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u

theorem solution :
∀ {G : Type u} [inst : Group.{u} G] [Finite.{u + 1} G] [Nontrivial.{u} G]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{u} G inst),
  @Exists.{u + 1} (@Subgroup.{u} G inst) fun (K : @Subgroup.{u} G inst) =>
    And (@Subgroup.Normal.{u} G inst K) (Nat.Prime (@Subgroup.index.{u} G inst K)) :=
  @LocalConjugacy.Proof.LocalConjugacy.supersolvable_exists_prime_index_preparedProof
