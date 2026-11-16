-- Prove2me | solution 1 for GoldreichAffine.Exponential.Supplement.binomial_transform_identity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:10:04.731806+00:00
-- url     : https://prove2.me/submissions/494be856-0a79-479d-aa71-23a397294446

import Mathlib
import Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
open scoped BigOperators
open MatousekLP.Codes (Word weight)
set_option autoImplicit false
open GoldreichAffine.Exponential.Supplement
open Polynomial

lemma gae_choose_mod2 (j k h : ℕ) :
    (((j + 2 ^ k).choose h : ℕ) : ZMod 2) =
      ((j.choose h : ℕ) : ZMod 2) + (if 2 ^ k ≤ h then ((j.choose (h - 2 ^ k) : ℕ) : ZMod 2) else 0) := by
  have hfrob : ((X : (ZMod 2)[X]) + 1) ^ (2 ^ k) = X ^ (2 ^ k) + 1 := by
    rw [add_pow_char_pow, one_pow]
  have h1 : (((X : (ZMod 2)[X]) + 1) ^ (j + 2 ^ k)).coeff h = (((j + 2 ^ k).choose h : ℕ) : ZMod 2) :=
    coeff_X_add_one_pow _ _ _
  rw [← h1, pow_add, hfrob, mul_add, mul_one, coeff_add, coeff_mul_X_pow']
  simp only [coeff_X_add_one_pow]
  split_ifs <;> ring

lemma gae_general (a : ℕ → ZMod 2) (j k w : ℕ) :
    binomialTransform a (j + 2 ^ k) w =
      binomialTransform a j w + binomialTransform a j (w + 2 ^ k) := by
  unfold binomialTransform
  simp_rw [gae_choose_mod2, add_mul, Finset.sum_add_distrib]
  congr 1
  · symm
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      have := Nat.zero_le (2 ^ k)
      omega
    · intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have : j + 2 ^ k + 1 = 2 ^ k + (j + 1) := by ring
    rw [this, Finset.sum_range_add]
    have hz : ∑ x ∈ Finset.range (2 ^ k),
        (if 2 ^ k ≤ x then ((j.choose (x - 2 ^ k) : ℕ) : ZMod 2) else 0) * a (w + x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_range] at hx
      rw [if_neg (by omega), zero_mul]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro x _
    rw [if_pos (by omega), Nat.add_sub_cancel_left]
    congr 2
    ring

theorem solution :
    (∀ (t : ℕ) (S0 : Finset ℕ), 2 ≤ t → S0 ⊆ Finset.range t → ∀ j k w : ℕ,
      binomialTransform (modSequence t S0) (j + 2 ^ k) w =
        binomialTransform (modSequence t S0) j w +
          binomialTransform (modSequence t S0) j (w + 2 ^ k)) ∧
    (∀ (a : ℕ → ZMod 2) (j k w : ℕ),
      binomialTransform a (j + 2 ^ k) w =
        binomialTransform a j w + binomialTransform a j (w + 2 ^ k)) :=
  ⟨fun t S0 _ _ j k w => gae_general _ j k w, gae_general⟩
