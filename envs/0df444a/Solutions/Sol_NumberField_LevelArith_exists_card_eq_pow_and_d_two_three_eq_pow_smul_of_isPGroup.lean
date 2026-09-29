-- Prove2me | solution 1 for NumberField.LevelArith.exists_card_eq_pow_and_d_two_three_eq_pow_smul_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c2ad497f-de32-5745-b3ba-7e3de7ad7d02

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_groupCohomology_Cores_exists_d_eq_corFin_resFin_sub_index_smul_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_card_eq_pow_and_d_two_three_eq_pow_smul_of_isPGroup

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

namespace CardKills3

open groupCohomology.Cores

variable {G : Type} [Group G]

theorem apply_one_eq_zero_of_d_eq_zero {R : Type} [CommRing R] (A : Rep.{0} R G)
    (f : (Fin 3 → G) → A) (hf : ((inhomogeneousCochains A).d 3 4).hom f = 0) : f 1 = 0 := by
  have h := congrFun hf 1
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_hom_apply] at h
  have hc : ∀ j : Fin 4, Fin.contractNth j (· * ·) (1 : Fin 4 → G) = 1 := fun j =>
    funext fun i => by simp [Fin.contractNth]
  simp only [hc, Pi.one_apply, map_one, Module.End.one_apply] at h
  rw [← Finset.sum_smul] at h
  have hs : ∑ x : Fin (3 + 1), (-1 : R) ^ ((x : ℕ) + 1) = 0 := by
    simp [Fin.sum_univ_succ, pow_succ]
  rw [hs, zero_smul, add_zero] at h
  exact h

variable (A : Rep.{0} ℤ G)

theorem resFin_bot (n : ℕ) (u : (Fin n → G) → A) (h : Fin n → (⊥ : Subgroup G)) :
    resFin (H := (⊥ : Subgroup G)) A n u h = u 1 := by
  unfold resFin
  congr 1
  funext i
  exact Subgroup.mem_bot.mp (h i).2

theorem corFin_zero [Finite G] (τ : Transversal (⊥ : Subgroup G)) (n : ℕ) :
    corFin (H := (⊥ : Subgroup G)) A τ n 0 = 0 := by
  funext g
  rw [corFin_apply]
  simp

end CardKills3

theorem solution
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (f : ((Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (hf : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0) :
    ∃ (k : ℕ) (b₀ : ((Fin 2 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))),
      Nat.card (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) = p ^ k ∧ ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b₀ = (p ^ k : ℤ) • f := by
  classical

  obtain ⟨k, hk⟩ := hG.exists_card_eq

  obtain ⟨τ⟩ := groupCohomology.Cores.Transversal.nonempty
    (H := (⊥ : Subgroup (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
  obtain ⟨b, hb, -⟩ :=
    groupCohomology.Cores.exists_d_eq_corFin_resFin_sub_index_smul_three _ ⊥ τ f hf
  have hres : groupCohomology.Cores.resFin
      (H := (⊥ : Subgroup (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
      ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) 3 f = 0 := by
    funext h
    rw [CardKills3.resFin_bot, CardKills3.apply_one_eq_zero_of_d_eq_zero _ f hf]
    rfl
  rw [hres, CardKills3.corFin_zero, zero_sub, Subgroup.index_bot, hk] at hb
  refine ⟨k, -b, hk, ?_⟩
  rw [map_neg, hb, neg_neg, ← Nat.cast_smul_eq_nsmul ℤ (p ^ k) f, Nat.cast_pow]

end S_NumberField_LevelArith_exists_card_eq_pow_and_d_two_three_eq_pow_smul_of_isPGroup
end P2MW
export P2MW.S_NumberField_LevelArith_exists_card_eq_pow_and_d_two_three_eq_pow_smul_of_isPGroup (solution)
