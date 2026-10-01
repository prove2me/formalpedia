-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.supersolvable_prime_index_above_normal_sylow
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:17:26.643455+00:00
-- url     : https://prove2.me/submissions/8f101289-195b-4002-b05d-603c93b179a0

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supersolvable_exists_prime_index

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy





universe u



private theorem supersolvable_prime_index_above_normal_sylow_preparedProof {G : Type*} [Group G] [Finite G]
    (hG : Supersolvable G) {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [P.toSubgroup.Normal] (hP : P.toSubgroup ≠ ⊤) :
    ∃ K : Subgroup G, K.Normal ∧ P.toSubgroup ≤ K ∧ K.index.Prime ∧ K.index ≠ p := by
  letI : Nontrivial (G ⧸ P.toSubgroup) := QuotientGroup.nontrivial_iff.mpr hP
  obtain ⟨D, hDn, hD⟩ := supersolvable_exists_prime_index
    (supersolvable_of_surjective hG (QuotientGroup.mk' P.toSubgroup)
      (QuotientGroup.mk'_surjective P.toSubgroup))
  letI := hDn
  let K := D.comap (QuotientGroup.mk' P.toSubgroup)
  have hPK : P.toSubgroup ≤ K := by
    simpa only [QuotientGroup.ker_mk'] using
      Subgroup.ker_le_comap (QuotientGroup.mk' P.toSubgroup) D
  have hKi : K.index = D.index := D.index_comap_of_surjective
    (QuotientGroup.mk'_surjective P.toSubgroup)
  refine ⟨K, inferInstance, hPK, hKi ▸ hD, fun he => ?_⟩
  have hd := Subgroup.index_dvd_of_le hPK
  rw [he] at hd
  exact P.not_dvd_index hd

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]









end Profinite
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{u_1} G inst) {p : Nat} [Fact (Nat.Prime p)]
  (P : @Sylow.{u_1} p G inst) [@Subgroup.Normal.{u_1} G inst (@Sylow.toSubgroup.{u_1} p G inst P)]
  (hP :
    @Ne.{u_1 + 1} (@Subgroup.{u_1} G inst) (@Sylow.toSubgroup.{u_1} p G inst P)
      (@Top.top.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instTop.{u_1} G inst))),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (K : @Subgroup.{u_1} G inst) =>
    And (@Subgroup.Normal.{u_1} G inst K)
      (And
        (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
          (@Sylow.toSubgroup.{u_1} p G inst P) K)
        (And (Nat.Prime (@Subgroup.index.{u_1} G inst K)) (@Ne.{1} Nat (@Subgroup.index.{u_1} G inst K) p))) :=
  @LocalConjugacy.Proof.LocalConjugacy.supersolvable_prime_index_above_normal_sylow_preparedProof
