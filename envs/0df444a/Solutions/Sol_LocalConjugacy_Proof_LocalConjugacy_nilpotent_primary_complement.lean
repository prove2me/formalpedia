-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.nilpotent_primary_complement
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:20:47.642796+00:00
-- url     : https://prove2.me/submissions/133404c7-669b-4ea5-8225-0b6880b6252e

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
open NilpotentCoefficients

section Factors
variable {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]

private theorem nilpotent_primary_complement_preparedProof (p : PrimeIndex G) :
    ∃ B : Subgroup G, B.Characteristic ∧ (Factor G p).IsComplement' B ∧
      (Nat.card (Factor G p)).Coprime (Nat.card B) := by
  classical
  letI (q : PrimeIndex G) := Fintype.ofFinite (Factor G q)
  let B : Subgroup G := ⨆ q : {q : PrimeIndex G // q ≠ p}, Factor G q.val
  have hi : iSupIndep (Factor G) := by
    apply Subgroup.independent_of_coprime_order factors_commute
    intro q r hqr
    simpa only [Nat.card_eq_fintype_card] using IsPGroup.coprime_card_of_ne q.val r.val
      (fun he => hqr (Subtype.ext he)) _ _ (primarySylow q).isPGroup' (primarySylow r).isPGroup'
  have hd : Disjoint (Factor G p) B := by
    exact (hi p).mono_right (iSup_le fun q => le_iSup_of_le q.val
      (le_iSup (fun _ : q.val ≠ p => Factor G q.val) q.property))
  have hs : Factor G p ⊔ B = ⊤ := by
    have hr : (⨆ q : PrimeIndex G, Factor G q) = ⊤ := by
      rw [← Subgroup.noncommPiCoprod_range (hcomm := factors_commute)]
      exact (Subgroup.noncommPiCoprod factors_commute).range_eq_top_of_surjective
        (productEquiv (N := G)).surjective
    rw [← hr]
    apply le_antisymm
    · exact sup_le (le_iSup (Factor G) p) (iSup_le fun q => le_iSup (Factor G) q.val)
    · apply iSup_le
      intro q
      by_cases he : q = p
      · exact he ▸ le_sup_left
      · exact (le_iSup (fun r : {r : PrimeIndex G // r ≠ p} => Factor G r.val) ⟨q, he⟩).trans le_sup_right
  have hc : (Factor G p).IsComplement' B := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd
    rw [← Subgroup.normal_mul, hs]
    rfl
  exact ⟨B, inferInstance, hc, hc.card_right ▸ (primarySylow p).card_coprime_index⟩



end Factors
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] [@Group.IsNilpotent.{u_1} G inst]
  (p : LocalConjugacy.Proof.LocalConjugacy.NilpotentCoefficients.PrimeIndex.{u_1} G),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (B : @Subgroup.{u_1} G inst) =>
    And (@Subgroup.Characteristic.{u_1} G inst B)
      (And
        (@Subgroup.IsComplement'.{u_1} G inst
          (@LocalConjugacy.Proof.LocalConjugacy.NilpotentCoefficients.Factor.{u_1} G inst p) B)
        (Nat.Coprime
          (Nat.card.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                (@LocalConjugacy.Proof.LocalConjugacy.NilpotentCoefficients.Factor.{u_1} G inst p) x))
          (Nat.card.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) B
                x)))) :=
  @LocalConjugacy.Proof.LocalConjugacy.nilpotent_primary_complement_preparedProof
