-- Prove2me | solution 1 for HScattered.Hyperplanes.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:10:33.045726+00:00
-- url     : https://prove2.me/submissions/fe74c6cf-4708-49a4-9fa5-0f31fd660625

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

set_option autoImplicit false

open HScattered.Hyperplanes

section gb
variable {q : ℝ}

lemma gb_D (hq : 1 < q) (k : ℕ) :
    ∏ i ∈ Finset.range k, (1 - q ^ (k - i)) = ∏ i ∈ Finset.range k, (1 - q ^ (i + 1)) := by
  rw [← Finset.prod_range_reflect (fun i => 1 - q ^ (i + 1)) k]
  apply Finset.prod_congr rfl
  intro i hi
  have := Finset.mem_range.mp hi
  have : k - 1 - i + 1 = k - i := by omega
  simp [this]

lemma gb_Dne (hq : 1 < q) (k : ℕ) : ∏ i ∈ Finset.range k, (1 - q ^ (i + 1)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have : 1 < q ^ (i + 1) := one_lt_pow₀ hq (by omega)
  linarith

lemma gb_eq (hq : 1 < q) {n k : ℕ} (h : k ≤ n) :
    gaussBinom q n k = (∏ i ∈ Finset.range k, (1 - q ^ (n - i))) /
      ∏ i ∈ Finset.range k, (1 - q ^ (i + 1)) := by
  unfold gaussBinom
  rw [if_neg (by omega), gb_D hq]

lemma gb_zero (hq : 1 < q) (n : ℕ) : gaussBinom q n 0 = 1 := by
  rw [gb_eq hq (Nat.zero_le _)]; simp

lemma gb_lt {n k : ℕ} (h : n < k) : gaussBinom q n k = 0 := by
  unfold gaussBinom; rw [if_pos h]

lemma gb_self (hq : 1 < q) (n : ℕ) : gaussBinom q n n = 1 := by
  rw [gb_eq hq le_rfl, ← gb_D hq]
  exact div_self (by rw [gb_D hq]; exact gb_Dne hq n)

lemma gb_pascal2 (hq : 1 < q) (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n (k + 1) + q ^ (n - k) * gaussBinom q n k := by
  rcases lt_trichotomy k n with hk | hk | hk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
    rw [gb_eq hq (by omega), gb_eq hq (by omega), gb_eq hq (by omega)]
    have h1 : ∏ i ∈ Finset.range (k + 1), (1 - q ^ (k + d + 1 + 1 - i)) =
        (1 - q ^ (k + d + 1 + 1)) * ∏ i ∈ Finset.range k, (1 - q ^ (k + d + 1 - i)) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero, mul_comm]
    have h2 : ∏ i ∈ Finset.range (k + 1), (1 - q ^ (k + d + 1 - i)) =
        (∏ i ∈ Finset.range k, (1 - q ^ (k + d + 1 - i))) * (1 - q ^ (d + 1)) := by
      rw [Finset.prod_range_succ]
      congr 3; omega
    have h3 : ∏ i ∈ Finset.range (k + 1), (1 - q ^ (i + 1)) =
        (∏ i ∈ Finset.range k, (1 - q ^ (i + 1))) * (1 - q ^ (k + 1)) := Finset.prod_range_succ _ _
    have hD := gb_Dne hq k
    have hk1 : (1 - q ^ (k + 1)) ≠ 0 := by
      have : 1 < q ^ (k + 1) := one_lt_pow₀ hq (by omega)
      linarith
    have e : k + d + 1 - k = d + 1 := by omega
    rw [h1, h2, h3, e]
    field_simp
    ring
  · subst hk
    rw [gb_self hq, gb_lt (by omega), gb_self hq]; simp
  · rw [gb_lt (by omega), gb_lt (by omega), gb_lt (by omega)]; simp

lemma gb_pascal1 (hq : 1 < q) (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = q ^ (k + 1) * gaussBinom q n (k + 1) + gaussBinom q n k := by
  rcases lt_trichotomy k n with hk | hk | hk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
    rw [gb_eq hq (by omega), gb_eq hq (by omega), gb_eq hq (by omega)]
    have h1 : ∏ i ∈ Finset.range (k + 1), (1 - q ^ (k + d + 1 + 1 - i)) =
        (1 - q ^ (k + d + 1 + 1)) * ∏ i ∈ Finset.range k, (1 - q ^ (k + d + 1 - i)) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero, mul_comm]
    have h2 : ∏ i ∈ Finset.range (k + 1), (1 - q ^ (k + d + 1 - i)) =
        (∏ i ∈ Finset.range k, (1 - q ^ (k + d + 1 - i))) * (1 - q ^ (d + 1)) := by
      rw [Finset.prod_range_succ]
      congr 3; omega
    have h3 : ∏ i ∈ Finset.range (k + 1), (1 - q ^ (i + 1)) =
        (∏ i ∈ Finset.range k, (1 - q ^ (i + 1))) * (1 - q ^ (k + 1)) := Finset.prod_range_succ _ _
    have hD := gb_Dne hq k
    have hk1 : (1 - q ^ (k + 1)) ≠ 0 := by
      have : 1 < q ^ (k + 1) := one_lt_pow₀ hq (by omega)
      linarith
    rw [h1, h2, h3]
    field_simp
    ring
  · subst hk
    rw [gb_self hq, gb_lt (by omega), gb_self hq]; simp
  · rw [gb_lt (by omega), gb_lt (by omega), gb_lt (by omega)]; simp

end gb

section st
variable {q : ℝ}

lemma stirling (hq : 1 < q) (x : ℝ) (k : ℕ) :
    x ^ k = ∑ j ∈ Finset.range (k + 1),
      gaussBinom q k j * ∏ l ∈ Finset.range j, (x - q ^ l) := by
  induction k with
  | zero => simp [gb_zero hq]
  | succ k ih =>
    set P : ℕ → ℝ := fun j => ∏ l ∈ Finset.range j, (x - q ^ l) with hP
    set A : ℕ → ℝ := fun j => gaussBinom q k j * P j with hA
    have hxP : ∀ j, x * P j = P (j + 1) + q ^ j * P j := by
      intro j; simp only [hP, Finset.prod_range_succ]; ring
    have h1 : x ^ (k + 1) = ∑ j ∈ Finset.range (k + 1),
        (gaussBinom q k j * P (j + 1) + q ^ j * A j) := by
      rw [pow_succ, mul_comm, ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have := hxP j
      simp only [hA]
      calc x * (gaussBinom q k j * ∏ l ∈ Finset.range j, (x - q ^ l))
          = gaussBinom q k j * (x * P j) := by simp only [hP]; ring
        _ = _ := by rw [this]; ring
    rw [h1, Finset.sum_add_distrib]
    have h2 : ∑ j ∈ Finset.range (k + 2), gaussBinom q (k + 1) j * P j =
        1 + ∑ j ∈ Finset.range (k + 1), gaussBinom q (k + 1) (j + 1) * P (j + 1) := by
      rw [Finset.sum_range_succ']; simp [hP, gb_zero hq, add_comm]
    have h3 : ∑ j ∈ Finset.range (k + 1), gaussBinom q (k + 1) (j + 1) * P (j + 1) =
        ∑ j ∈ Finset.range (k + 1), gaussBinom q k j * P (j + 1) +
        ∑ j ∈ Finset.range (k + 1), q ^ (j + 1) * A (j + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [gb_pascal1 hq k j]; simp only [hA]; ring
    have h4 : 1 + ∑ j ∈ Finset.range (k + 1), q ^ (j + 1) * A (j + 1) =
        ∑ j ∈ Finset.range (k + 1), q ^ j * A j := by
      have : ∑ j ∈ Finset.range (k + 2), q ^ j * A j =
          ∑ j ∈ Finset.range (k + 1), q ^ j * A j + q ^ (k + 1) * A (k + 1) :=
        Finset.sum_range_succ _ _
      have h0 : A (k + 1) = 0 := by simp [hA, gb_lt (show k < k + 1 by omega)]
      rw [Finset.sum_range_succ' (fun j => q ^ j * A j) (k + 1), h0] at this
      simp only [hA, hP, Finset.prod_range_zero, gb_zero hq] at this
      simp only [hA, hP]
      linarith
    rw [h2, h3]
    simp only [hA] at h4 ⊢
    linarith

end st

theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (k : ℕ) (hk : k ≤ h + 1) :
    (alphaSum F K U k : ℝ) =
      ∑ j ∈ Finset.range (k + 1),
        gaussBinom (Fintype.card F : ℝ) k j * (betaSum F K U j : ℝ) := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set c : ℕ → ℝ := fun i => (hCount F K U i : ℝ) * (q ^ Module.finrank F K - 1) with hc
  have hα : (alphaSum F K U k : ℝ) =
      ∑ i ∈ Finset.range (Module.finrank F U + 1), c i * (q ^ i) ^ k := by
    unfold alphaSum
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    simp only [hc, ← pow_mul, mul_comm i k]
    rfl
  have hβ : ∀ j, (betaSum F K U j : ℝ) =
      ∑ i ∈ Finset.range (Module.finrank F U + 1), c i * ∏ l ∈ Finset.range j, (q ^ i - q ^ l) := by
    intro j
    unfold betaSum
    push_cast
    rfl
  rw [hα]
  simp only [hβ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [stirling hq (q ^ i) k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
