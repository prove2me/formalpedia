-- Prove2me | solution 1 for HScattered.Hyperplanes.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:10:30.771484+00:00
-- url     : https://prove2.me/submissions/e0d66d0e-1448-4f5f-87e1-329092b21eed

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_sigma

set_option autoImplicit false

lemma ch2 (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  have := Nat.choose_succ_succ' j 1
  rw [Nat.choose_one_right] at this
  norm_num at this
  omega


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

lemma sigma_zero_left (q : ℝ) (k : ℕ) : sigma q k 0 = 1 := by
  simp [sigma]

lemma sigma_succ (q : ℝ) (k l : ℕ) :
    sigma q (k + 1) (l + 1) = sigma q k (l + 1) + q ^ (k + 1) * sigma q k l := by
  unfold sigma
  have hn : (k + 1) ∉ Finset.range (k + 1) := by simp
  have hmem : ∀ T ∈ (Finset.range (k + 1)).powersetCard l, (k + 1) ∉ T := by
    intro T hT h
    exact hn ((Finset.mem_powersetCard.mp hT).1 h)
  rw [Finset.range_add_one (n := k + 1), Finset.powersetCard_succ_insert hn,
    Finset.sum_union, Finset.sum_image, Finset.mul_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.sum_insert (hmem T hT), pow_add, mul_comm]
  · intro T hT T' hT' h
    rw [← Finset.erase_insert (hmem T hT), h, Finset.erase_insert (hmem T' hT')]
  · rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨T', hT'1, rfl⟩ := Finset.mem_image.mp hT'
    have := (Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self _ _)
    exact hn this

lemma lem55 (q : ℝ) (hq : 1 < q) (k : ℕ) : ∀ l : ℕ,
    sigma q k l = q ^ (l.choose 2) * gaussBinom q (k + 1) l := by
  induction k with
  | zero =>
    intro l
    rcases l with _ | _ | l
    · simp [sigma_zero_left, gb_zero hq]
    · simp [sigma, gb_self hq, Finset.powersetCard_one]
    · rw [gb_lt (by omega)]
      simp [sigma]
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]; simp
  | succ k ih =>
    intro l
    rcases l with _ | l
    · simp [sigma_zero_left, gb_zero hq]
    · rw [sigma_succ, ih, ih]
      rw [gb_pascal2 hq (k + 1) l]
      rcases le_or_gt l (k + 1) with hl | hl
      · have e : l.choose 2 + l = (l + 1).choose 2 := (ch2 l).symm
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hl
        have : q ^ (k + 1) * q ^ l.choose 2 = q ^ (l + 1).choose 2 * q ^ (k + 1 - l) := by
          rw [← pow_add, ← pow_add, ← e]; congr 1; omega
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← this]
      · rw [gb_lt (by omega : k + 1 < l)]
        rw [gb_lt (by omega : k + 1 < l + 1)]
        simp

theorem solution (q : ℝ) (hq : 1 < q) (k l : ℕ) :
    sigma q k l = q ^ (l.choose 2) * gaussBinom q (k + 1) l := lem55 q hq k l
