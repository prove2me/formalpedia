-- Prove2me | solution 1 for HScattered.Hyperplanes.corollary_5_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:08:38.80053+00:00
-- url     : https://prove2.me/submissions/6c20efa1-5281-4d1f-b735-35e8aa19442d

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_qPoch

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

section qb
variable {q : ℝ}

lemma qp_succ (a q : ℝ) (k : ℕ) : qPoch a q (k + 1) = qPoch a q k * (1 - a * q ^ k) := by
  unfold qPoch; rw [Finset.prod_range_succ]

lemma qp_zero (a q : ℝ) : qPoch a q 0 = 1 := by simp [qPoch]

lemma qb1 (hq : 1 < q) (a b : ℝ) (n : ℕ) :
    qPoch (a * b) q n = ∑ k ∈ Finset.range (n + 1),
        b ^ k * gaussBinom q n k * qPoch a q k * qPoch b q (n - k) := by
  induction n with
  | zero => simp [qp_zero, gb_zero hq]
  | succ n ih =>
    rw [qp_succ, ih]
    set A : ℕ → ℝ := fun k => b ^ k * gaussBinom q n k * qPoch a q k * qPoch b q (n + 1 - k) with hA
    set B : ℕ → ℝ := fun j => b ^ (j + 1) * (q ^ (n - j) * gaussBinom q n j) * qPoch a q (j + 1) *
      qPoch b q (n - j) with hB
    have h1 : ∀ j, b ^ (j + 1) * gaussBinom q (n + 1) (j + 1) * qPoch a q (j + 1) *
        qPoch b q (n + 1 - (j + 1)) = A (j + 1) + B j := by
      intro j
      rw [gb_pascal2 hq n j]
      simp only [hA, hB, Nat.add_sub_add_right]
      ring
    have h0 : b ^ 0 * gaussBinom q (n + 1) 0 * qPoch a q 0 * qPoch b q (n + 1 - 0) = A 0 := by
      simp [hA, gb_zero hq]
    rw [Finset.sum_range_succ' _ (n + 1)]
    simp only [h1, h0]
    rw [Finset.sum_add_distrib]
    have h2 : ∑ j ∈ Finset.range (n + 1), A (j + 1) + A 0 = ∑ k ∈ Finset.range (n + 1), A k := by
      rw [← Finset.sum_range_succ' A (n + 1), Finset.sum_range_succ]
      simp [hA, gb_lt (show n < n + 1 by omega)]
    rw [add_assoc, add_comm (∑ j ∈ Finset.range (n + 1), B j), ← add_assoc, h2,
      ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have e1 : k + d + 1 - k = d + 1 := by omega
    have e2 : k + d - k = d := by omega
    simp only [hA, hB, e1, e2, qp_succ]
    have : q ^ (k + d) = q ^ k * q ^ d := pow_add _ _ _
    rw [this]
    ring

lemma qb2 (hq : 1 < q) (a b : ℝ) (n : ℕ) :
    qPoch (a * b) q n = ∑ k ∈ Finset.range (n + 1),
        a ^ (n - k) * gaussBinom q n k * qPoch a q k * qPoch b q (n - k) := by
  induction n with
  | zero => simp [qp_zero, gb_zero hq]
  | succ n ih =>
    rw [qp_succ, ih]
    set C : ℕ → ℝ := fun m => a ^ (n + 1 - m) * (q ^ m * gaussBinom q n m) * qPoch a q m *
      qPoch b q (n + 1 - m) with hC
    set D : ℕ → ℝ := fun j => a ^ (n - j) * gaussBinom q n j * (qPoch a q j * (1 - a * q ^ j)) *
      qPoch b q (n - j) with hD
    have h1 : ∀ j, a ^ (n + 1 - (j + 1)) * gaussBinom q (n + 1) (j + 1) * qPoch a q (j + 1) *
        qPoch b q (n + 1 - (j + 1)) = C (j + 1) + D j := by
      intro j
      rw [gb_pascal1 hq n j]
      simp only [hC, hD, Nat.add_sub_add_right, qp_succ]
      ring
    have h0 : a ^ (n + 1 - 0) * gaussBinom q (n + 1) 0 * qPoch a q 0 * qPoch b q (n + 1 - 0) =
        C 0 := by
      simp [hC, gb_zero hq]
    rw [Finset.sum_range_succ' _ (n + 1)]
    simp only [h1, h0]
    rw [Finset.sum_add_distrib]
    have h2 : ∑ j ∈ Finset.range (n + 1), C (j + 1) + C 0 = ∑ k ∈ Finset.range (n + 1), C k := by
      rw [← Finset.sum_range_succ' C (n + 1), Finset.sum_range_succ]
      simp [hC, gb_lt (show n < n + 1 by omega)]
    rw [add_assoc, add_comm (∑ j ∈ Finset.range (n + 1), D j), ← add_assoc, h2,
      ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have e1 : k + d + 1 - k = d + 1 := by omega
    have e2 : k + d - k = d := by omega
    simp only [hC, hD, e1, e2, qp_succ, pow_succ]
    have : q ^ (k + d) = q ^ k * q ^ d := pow_add _ _ _
    rw [this]
    ring

lemma cor53a (hq : 1 < q) (n r s m : ℕ) (hm : s * m = n * r) :
    qPoch (q ^ (-(n : ℤ))) q s = ∑ j ∈ Finset.range (s + 1),
        q ^ ((j : ℤ) * ((m : ℤ) - n)) * gaussBinom q s j *
          qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) := by
  have hq0 : q ≠ 0 := by positivity
  have h := qb1 hq (q ^ (-(m : ℤ))) (q ^ ((m : ℤ) - n)) s
  rw [← zpow_add₀ hq0] at h
  have e : -(m : ℤ) + ((m : ℤ) - n) = -(n : ℤ) := by ring
  rw [e] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  have : q ^ ((j : ℤ) * ((m : ℤ) - n)) = (q ^ ((m : ℤ) - n)) ^ j := by
    rw [mul_comm, zpow_mul]; simp
  rw [this]

lemma cor53b (hq : 1 < q) (n r s m : ℕ) (hm : s * m = n * r) :
    qPoch (q ^ (-(n : ℤ))) q s = q ^ (-((n : ℤ) * r)) * ∑ j ∈ Finset.range (s + 1),
        q ^ ((j : ℤ) * m) * gaussBinom q s j *
          qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) := by
  have hq0 : q ≠ 0 := by positivity
  have h := qb2 hq (q ^ (-(m : ℤ))) (q ^ ((m : ℤ) - n)) s
  rw [← zpow_add₀ hq0] at h
  have e : -(m : ℤ) + ((m : ℤ) - n) = -(n : ℤ) := by ring
  rw [e] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hnr : ((n : ℤ) * r) = (s : ℤ) * m := by exact_mod_cast hm.symm
  have : q ^ (-((n : ℤ) * r)) * q ^ ((j : ℤ) * m) = (q ^ (-(m : ℤ))) ^ (s - j) := by
    rw [← zpow_add₀ hq0, ← zpow_natCast, ← zpow_mul, hnr]
    congr 1
    push_cast [Nat.cast_sub (show j ≤ s by omega)]
    ring
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, this]

end qb

theorem solution (q : ℝ) (hq : 1 < q) (n r s m : ℕ) (hs : 0 < s) (hm : s * m = n * r) :
    qPoch (q ^ (-(n : ℤ))) q s = ∑ j ∈ Finset.range (s + 1),
        q ^ ((j : ℤ) * ((m : ℤ) - n)) * gaussBinom q s j *
          qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) ∧
      qPoch (q ^ (-(n : ℤ))) q s = q ^ (-((n : ℤ) * r)) * ∑ j ∈ Finset.range (s + 1),
        q ^ ((j : ℤ) * m) * gaussBinom q s j *
          qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) :=
  ⟨cor53a hq n r s m hm, cor53b hq n r s m hm⟩
