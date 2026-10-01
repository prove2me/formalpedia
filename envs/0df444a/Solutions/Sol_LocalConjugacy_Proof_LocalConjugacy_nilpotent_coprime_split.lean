-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.nilpotent_coprime_split
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:28:38.383254+00:00
-- url     : https://prove2.me/submissions/5d81e9ad-56ed-4645-a189-27f44b60f5c7

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_nilpotent_primary_complement

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open NilpotentCoefficients

section Factors
variable {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]



private theorem nilpotent_coprime_split_preparedProof (h : ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p G) :
    ∃ A B : Subgroup G, A.Characteristic ∧ B.Characteristic ∧
      A.IsComplement' B ∧ (Nat.card A).Coprime (Nat.card B) ∧ A ≠ ⊥ ∧ B ≠ ⊥ := by
  classical
  have hn : Nat.card G ≠ 1 := by
    intro he
    letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp he).1
    exact h ⟨2, Nat.prime_two, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
  let q : PrimeIndex G := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.card_pos.ne'⟩⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB, hc, hcop⟩ := nilpotent_primary_complement q
  refine ⟨Factor G q, B, inferInstance, hB, hc, hcop,
    (primarySylow q).ne_bot_of_dvd_card hpd, ?_⟩
  intro he
  have htop := hc.sup_eq_top
  rw [he, sup_bot_eq] at htop
  have hpg : IsPGroup p (Factor G q) := (primarySylow q).isPGroup'
  rw [htop] at hpg
  exact h ⟨p, hp, hpg.of_equiv Subgroup.topEquiv⟩

end Factors
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] [@Group.IsNilpotent.{u_1} G inst]
  (h : Not (@Exists.{1} Nat fun (p : Nat) => And (Nat.Prime p) (@IsPGroup.{u_1} p G inst))),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (A : @Subgroup.{u_1} G inst) =>
    @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (B : @Subgroup.{u_1} G inst) =>
      And (@Subgroup.Characteristic.{u_1} G inst A)
        (And (@Subgroup.Characteristic.{u_1} G inst B)
          (And (@Subgroup.IsComplement'.{u_1} G inst A B)
            (And
              (Nat.Coprime
                (Nat.card.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      A x))
                (Nat.card.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      B x)))
              (And
                (@Ne.{u_1 + 1} (@Subgroup.{u_1} G inst) A
                  (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst)))
                (@Ne.{u_1 + 1} (@Subgroup.{u_1} G inst) B
                  (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst))))))) :=
  @LocalConjugacy.Proof.LocalConjugacy.nilpotent_coprime_split_preparedProof
