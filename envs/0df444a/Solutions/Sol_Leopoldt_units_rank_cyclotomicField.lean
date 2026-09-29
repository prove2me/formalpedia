-- Prove2me | solution 1 for Leopoldt.units_rank_cyclotomicField
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:17:43.419196+00:00
-- url     : https://prove2.me/submissions/08274715-fa79-44df-8894-0b0ac1579e18

import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open NumberField

theorem solution (n : ℕ) :
    Units.rank (CyclotomicField n ℚ) = n.totient / 2 - 1 := by
  rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  have key := InfinitePlace.card_add_two_mul_card_eq_rank (CyclotomicField n ℚ)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hf : Module.finrank ℚ (CyclotomicField 0 ℚ) = 1 := by
      have : Polynomial.IsSplittingField ℚ ℚ (Polynomial.cyclotomic 0 ℚ) :=
        Polynomial.isSplittingField_C 1
      let e : ℚ ≃ₗ[ℚ] (CyclotomicField 0 ℚ) :=
        (Polynomial.IsSplittingField.algEquiv ℚ (Polynomial.cyclotomic 0 ℚ)).toLinearEquiv
      simp [← LinearEquiv.finrank_eq e, Module.finrank_self]
    rw [InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hf,
      InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hf]
    simp
  · have : NeZero n := ⟨hn.ne'⟩
    have : NeZero (n : ℚ) := ⟨by exact_mod_cast hn.ne'⟩
    have : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) := by
      convert CyclotomicField.isCyclotomicExtension n ℚ <;> rfl
    have h2 := IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two n (CyclotomicField n ℚ)
    have hf := IsCyclotomicExtension.finrank (n := n) (CyclotomicField n ℚ)
      (Polynomial.cyclotomic.irreducible_rat hn)
    rw [hf] at key
    rw [h2] at key ⊢
    by_cases h : 2 < n
    · obtain ⟨k, hk⟩ := Nat.totient_even h
      rw [hk] at key ⊢
      omega
    · have : n.totient = 1 := by
        have h3 : n = 1 ∨ n = 2 := by omega
        rcases h3 with rfl | rfl <;> simp
      rw [this] at key ⊢
      omega
