-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.locally_contains
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:38:46.041813+00:00
-- url     : https://prove2.me/submissions/9a868bb1-faec-427a-aecf-2eeceb08f311

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_of_index

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

/-!
The imprimitive wreath product `C₃ wr S₃`, of order 162, acting on nine
points. Its normal Heisenberg subgroup is the kernel of the base-sum/sign
map to `C₃ × C₂`. The chosen cyclic complement translates block zero and
interchanges the other two blocks. Its Sylow subgroups have disjoint fixed
point sets. This is the second example in the manuscript.
-/

namespace LocalConjugacy.HeisenbergExample








set_option maxRecDepth 10000
set_option maxHeartbeats 0












































































private theorem P3_le : P3 ≤ J := by rintro x ⟨z, rfl⟩; exact ⟨(z, 1), rfl⟩
private theorem P2_le : P2 ≤ J := by rintro x ⟨z, rfl⟩; exact ⟨(1, z), rfl⟩
private theorem card_P3 : Fintype.card P3 = 3 := by decide
private theorem card_P2 : Fintype.card P2 = 2 := by decide

private theorem index_P3 : (P3.subgroupOf J).index = 2 := by
  have h := (P3.subgroupOf J).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P3_le).toEquiv,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_P3, card_J] at h
  omega

private theorem index_P2 : (P2.subgroupOf J).index = 3 := by
  have h := (P2.subgroupOf J).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P2_le).toEquiv,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_P2, card_J] at h
  omega

private theorem sylow_P3 : IsSylowPro 3 J P3 := by
  apply isSylowPro_of_index J P3 P3_le
  · apply IsPGroup.of_card (n := 1)
    simp [Nat.card_eq_fintype_card, card_P3]
  · rw [index_P3]; decide

private theorem sylow_P2 : IsSylowPro 2 J P2 := by
  apply isSylowPro_of_index J P2 P2_le
  · apply IsPGroup.of_card (n := 1)
    simp [Nat.card_eq_fintype_card, card_P2]
  · rw [index_P2]; decide

private theorem locally_contains_preparedProof : LocallyContains H J := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    refine ⟨P2, sylow_P2, 1, ?_⟩
    rintro x ⟨y, ⟨z, rfl⟩, rfl⟩
    exact (by decide : ∀ z : C2, (1 : G) * sectionMap (1, z) * 1⁻¹ ∈ H) z
  by_cases hp3 : p = 3
  · subst p
    refine ⟨P3, sylow_P3, shift, ?_⟩
    rintro x ⟨y, ⟨z, rfl⟩, rfl⟩
    exact (by decide : ∀ z : C3, shift * sectionMap (z, 1) * shift⁻¹ ∈ H) z
  refine ⟨⊥, isSylowPro_of_index J ⊥ bot_le (IsPGroup.of_bot) ?_, 1, ?_⟩
  · rw [Subgroup.bot_subgroupOf, Subgroup.index_bot, Nat.card_eq_fintype_card, card_J]
    intro h
    have h' : p ∣ 2 * 3 := h
    rcases hp.dvd_mul.mp h' with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h2)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h3)
  · simp [conjugate]














end LocalConjugacy.HeisenbergExample

end LocalConjugacy.Proof

end

theorem solution :
@LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{0} LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.G
  (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.B
    LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.S
    (@Pi.group.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun (a : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
        LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.C3)
      fun (i : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
      @Multiplicative.group.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@AddGroupWithOne.toAddGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  Nat.fact_prime_three))))))
    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.action)
  LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.instTopologicalSpaceG
  LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.H LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.J :=
  @LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.locally_contains_preparedProof
