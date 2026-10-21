-- Prove2me | solution 1 for HScattered.Hyperplanes.proposition_5_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:13:51.537572+00:00
-- url     : https://prove2.me/submissions/cef3358a-ea7a-4319-85f0-ce7ad9221104

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_qPoch
import Definitions.Def_HScattered_Hyperplanes_abSums

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

section gauss
variable {q : ℝ}

lemma gauss (hq : 1 < q) (x : ℝ) (N : ℕ) :
    ∏ i ∈ Finset.range N, (1 + x * q ^ i) =
      ∑ m ∈ Finset.range (N + 1), q ^ (m.choose 2) * gaussBinom q N m * x ^ m := by
  induction N with
  | zero => simp [gb_zero hq]
  | succ N ih =>
    rw [Finset.prod_range_succ, ih]
    set S : ℕ → ℝ := fun m => q ^ (m.choose 2) * gaussBinom q N m * x ^ m with hS
    have h1 : ∑ m ∈ Finset.range (N + 1 + 1), q ^ (m.choose 2) * gaussBinom q (N + 1) m * x ^ m =
        ∑ j ∈ Finset.range (N + 1), q ^ ((j + 1).choose 2) * gaussBinom q (N + 1) (j + 1) *
          x ^ (j + 1) + 1 := by
      rw [Finset.sum_range_succ']; simp [gb_zero hq]
    have h2 : ∑ j ∈ Finset.range (N + 1), q ^ ((j + 1).choose 2) * gaussBinom q (N + 1) (j + 1) *
          x ^ (j + 1) = ∑ j ∈ Finset.range (N + 1), S (j + 1) +
        ∑ j ∈ Finset.range (N + 1), S j * (x * q ^ N) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      rw [gb_pascal2 hq N j]
      have e : q ^ ((j + 1).choose 2) * q ^ (N - j) = q ^ (j.choose 2) * q ^ N := by
        rw [← pow_add, ← pow_add, ch2]; congr 1; omega
      simp only [hS]
      linear_combination (gaussBinom q N j * x ^ (j + 1)) * e
    have h3 : ∑ j ∈ Finset.range (N + 1), S (j + 1) + S 0 = ∑ m ∈ Finset.range (N + 1), S m := by
      rw [← Finset.sum_range_succ' S (N + 1), Finset.sum_range_succ]
      simp [hS, gb_lt (show N < N + 1 by omega)]
    have h4 : S 0 = 1 := by simp [hS, gb_zero hq]
    rw [h1, h2, ← Finset.sum_mul]
    rw [h4] at h3
    linarith

lemma gauss_neg (hq : 1 < q) (x : ℝ) (N : ℕ) :
    ∏ i ∈ Finset.range N, (1 - x * q ^ i) =
      ∑ m ∈ Finset.range (N + 1), (-1) ^ m * q ^ (m.choose 2) * gaussBinom q N m * x ^ m := by
  have := gauss hq (-x) N
  simp only [neg_mul, ← sub_eq_add_neg] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro m _
  rw [neg_pow]; ring

lemma gb_fact (hq : 1 < q) {n k : ℕ} (h : k ≤ n) :
    gaussBinom q n k * (∏ i ∈ Finset.range k, (1 - q ^ (i + 1))) *
      ∏ i ∈ Finset.range (n - k), (1 - q ^ (i + 1)) = ∏ i ∈ Finset.range n, (1 - q ^ (i + 1)) := by
  rw [gb_eq hq h, div_mul_cancel₀ _ (gb_Dne hq k)]
  conv_rhs => rw [show n = (n - k) + k by omega, Finset.prod_range_add]
  rw [mul_comm]
  congr 1
  rw [← Finset.prod_range_reflect]
  apply Finset.prod_congr rfl
  intro i hi
  have := Finset.mem_range.mp hi
  congr 3
  omega

lemma gb_mul (hq : 1 < q) {k i j : ℕ} (hji : j ≤ i) (hik : i ≤ k) :
    gaussBinom q k i * gaussBinom q i j = gaussBinom q k j * gaussBinom q (k - j) (i - j) := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ, ∀ n, D n = ∏ l ∈ Finset.range n, (1 - q ^ (l + 1)) :=
    ⟨_, fun n => rfl⟩
  have hDne : ∀ n, D n ≠ 0 := fun n => by rw [hDdef]; exact gb_Dne hq n
  have e1 := gb_fact hq hik
  have e2 := gb_fact hq hji
  have e3 := gb_fact hq (show j ≤ k by omega)
  have e4 := gb_fact hq (show i - j ≤ k - j by omega)
  have a1 : k - i = (k - j) - (i - j) := by omega
  rw [← a1] at e4
  simp only [← hDdef] at e1 e2 e3 e4
  have h1 := hDne k; have h2 := hDne i; have h3 := hDne j; have h4 := hDne (k - i)
  have h5 := hDne (i - j); have h6 := hDne (k - j)
  have g1 : gaussBinom q k i = D k / (D i * D (k - i)) := by
    rw [eq_div_iff (mul_ne_zero h2 h4), ← e1]; ring
  have g2 : gaussBinom q i j = D i / (D j * D (i - j)) := by
    rw [eq_div_iff (mul_ne_zero h3 h5), ← e2]; ring
  have g3 : gaussBinom q k j = D k / (D j * D (k - j)) := by
    rw [eq_div_iff (mul_ne_zero h3 h6), ← e3]; ring
  have g4 : gaussBinom q (k - j) (i - j) = D (k - j) / (D (i - j) * D (k - i)) := by
    rw [eq_div_iff (mul_ne_zero h5 h4), ← e4]; ring
  rw [g1, g2, g3, g4]
  field_simp

end gauss

lemma ch2_add (j m : ℕ) : (j + m).choose 2 = j.choose 2 + m.choose 2 + j * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, ch2, ch2, ih, Nat.mul_succ]; omega

lemma ch2_double (k : ℕ) : 2 * k.choose 2 + k = k * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [ch2]; nlinarith [ih]

section orth
variable {q : ℝ}

lemma sum_shift (hq : 1 < q) (j k : ℕ) (hj : j ≤ k) (w : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k + 1), w i * gaussBinom q k i * gaussBinom q i j =
      ∑ m ∈ Finset.range (k - j + 1), w (j + m) * (gaussBinom q k j * gaussBinom q (k - j) m) := by
  have e : k + 1 = j + (k - j + 1) := by omega
  rw [e, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun i hi => by rw [gb_lt (Finset.mem_range.mp hi), mul_zero]), zero_add]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' := Finset.mem_range.mp hm
  have := gb_mul hq (k := k) (i := j + m) (j := j) (by omega) (by omega)
  rw [Nat.add_sub_cancel_left] at this
  rw [mul_assoc, this]

lemma orth_gen (hq : 1 < q) (j k : ℕ) (hjk : j < k) (lam : ℤ)
    (h0 : 0 ≤ -((j : ℤ) + lam)) (h1 : -((j : ℤ) + lam) < (k : ℤ) - j) :
    ∑ i ∈ Finset.range (k + 1), ((-1 : ℝ) ^ i * q ^ ((i.choose 2 : ℤ) + lam * i)) *
      gaussBinom q k i * gaussBinom q i j = 0 := by
  have hq0 : q ≠ 0 := by positivity
  rw [sum_shift hq j k hjk.le]
  have key : ∀ m : ℕ, ((-1 : ℝ) ^ (j + m) * q ^(((j + m).choose 2 : ℤ) + lam * ((j + m : ℕ) : ℤ))) *
      (gaussBinom q k j * gaussBinom q (k - j) m) =
      ((-1) ^ j * q ^ ((j.choose 2 : ℤ) + lam * j) * gaussBinom q k j) *
        ((-1) ^ m * q ^ (m.choose 2) * gaussBinom q (k - j) m * (q ^ ((j : ℤ) + lam)) ^ m) := by
    intro m
    have e : (((j + m).choose 2 : ℕ) : ℤ) + lam * ((j + m : ℕ) : ℤ) =
        (((j.choose 2 : ℕ) : ℤ) + lam * j) + ((m.choose 2 : ℕ) : ℤ) + ((j : ℤ) + lam) * m := by
      rw [ch2_add]; push_cast; ring
    rw [e, zpow_add₀ hq0, zpow_add₀ hq0, zpow_mul, zpow_natCast, zpow_natCast, pow_add]
    ring
  simp only [key]
  rw [← Finset.mul_sum, ← gauss_neg hq]
  have : ∏ l ∈ Finset.range (k - j), (1 - q ^ ((j : ℤ) + lam) * q ^ l) = 0 := by
    apply Finset.prod_eq_zero (i := (-((j : ℤ) + lam)).toNat)
    · rw [Finset.mem_range]; omega
    · have : (((-((j : ℤ) + lam)).toNat : ℕ) : ℤ) = -((j : ℤ) + lam) := Int.toNat_of_nonneg h0
      rw [← zpow_natCast, this, ← zpow_add₀ hq0]; simp
  rw [this, mul_zero]

lemma orth_diag (k : ℕ) (hq : 1 < q) (w : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k + 1), w i * gaussBinom q k i * gaussBinom q i k = w k := by
  rw [Finset.sum_eq_single k]
  · rw [gb_self hq]; ring
  · intro i hi hik
    have := Finset.mem_range.mp hi
    rw [gb_lt (by omega : i < k)]; ring
  · intro h; simp at h

lemma orth_gt (hq : 1 < q) (j k : ℕ) (hjk : k < j) (w : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k + 1), w i * gaussBinom q k i * gaussBinom q i j = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have := Finset.mem_range.mp hi
  rw [gb_lt (by omega : i < j)]; ring

end orth

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

section ab
variable {q : ℝ}

lemma gb_symm (hq : 1 < q) {n k : ℕ} (h : k ≤ n) : gaussBinom q n (n - k) = gaussBinom q n k := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ, ∀ n, D n = ∏ l ∈ Finset.range n, (1 - q ^ (l + 1)) :=
    ⟨_, fun n => rfl⟩
  have e1 := gb_fact hq h
  have e2 := gb_fact hq (show n - k ≤ n by omega)
  have e3 : n - (n - k) = k := by omega
  rw [e3] at e2
  simp only [← hDdef] at e1 e2
  have h1 : D k ≠ 0 := by rw [hDdef]; exact gb_Dne hq k
  have h2 : D (n - k) ≠ 0 := by rw [hDdef]; exact gb_Dne hq (n - k)
  have : gaussBinom q n (n - k) * (D (n - k) * D k) = gaussBinom q n k * (D (n - k) * D k) := by
    calc _ = gaussBinom q n (n - k) * D (n - k) * D k := by ring
      _ = D n := e2
      _ = gaussBinom q n k * D k * D (n - k) := e1.symm
      _ = _ := by ring
  exact mul_right_cancel₀ (mul_ne_zero h2 h1) this

/-- the exponent `(s-k)(m-n) + C(s-k,2)` of §5.4 -/
def Ek (s m n k : ℕ) : ℤ := ((s : ℤ) - k) * ((m : ℤ) - n) + ((s - k).choose 2 : ℕ)

lemma abTerm_t_sum (hq : 1 < q) (n s m j k : ℕ) (hj : j ≤ s) :
    ∑ t ∈ Finset.range (s + 1), abTerm q n s m j k t =
      (q ^ ((m : ℤ) * j + Ek s m n k) * gaussBinom q s k * gaussBinom q k j * (-1) ^ k) *
        qPoch (q ^ (-(m : ℤ))) q j := by
  have hq0 : q ≠ 0 := by positivity
  have hsub : Finset.range (j + 1) ⊆ Finset.range (s + 1) := by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  rw [← Finset.sum_subset hsub (fun t _ ht => by
    have := Finset.mem_range.not.mp ht
    simp [abTerm, gb_lt (show j < t by omega)])]
  have key : ∀ t : ℕ, abTerm q n s m j k t =
      (q ^ ((m : ℤ) * j + Ek s m n k) * gaussBinom q s k * gaussBinom q k j * (-1) ^ k) *
        ((-1) ^ t * q ^ (t.choose 2) * gaussBinom q j t * (q ^ (-(m : ℤ))) ^ t) := by
    intro t
    unfold abTerm
    have e : (m : ℤ) * j - (m : ℤ) * t + ((s : ℤ) - k) * ((m : ℤ) - n) + ((s - k).choose 2 : ℕ) +
        (t.choose 2 : ℕ) = ((m : ℤ) * j + Ek s m n k) + ((t.choose 2 : ℕ) : ℤ) + (-(m : ℤ)) * t := by
      unfold Ek; ring
    rw [e, zpow_add₀ hq0, zpow_add₀ hq0, zpow_mul, zpow_natCast, zpow_natCast, pow_add]
    ring
  simp only [key]
  rw [← Finset.mul_sum, ← gauss_neg hq]
  rfl

lemma Ek_sum (hq : 1 < q) (s m n j : ℕ) (hj : j ≤ s) :
    ∑ k ∈ Finset.range (s + 1), (q ^ (Ek s m n k) * gaussBinom q s k * gaussBinom q k j * (-1) ^ k) =
      (-1) ^ s * gaussBinom q s j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) := by
  have hq0 : q ≠ 0 := by positivity
  have h1 : ∀ k ∈ Finset.range (s + 1), q ^ (Ek s m n k) * gaussBinom q s k * gaussBinom q k j * (-1) ^ k =
      (q ^ (Ek s m n k) * (-1) ^ k) * gaussBinom q s k * gaussBinom q k j := by
    intro k _; ring
  rw [Finset.sum_congr rfl h1, sum_shift hq j s hj (fun k => q ^ (Ek s m n k) * (-1) ^ k)]
  set N := s - j with hN
  rw [← Finset.sum_range_reflect _ (N + 1)]
  have h2 : ∀ u ∈ Finset.range (N + 1),
      (fun k => q ^ (Ek s m n k) * (-1) ^ k) (j + (N + 1 - 1 - u)) *
        (gaussBinom q s j * gaussBinom q (s - j) (N + 1 - 1 - u)) =
      ((-1) ^ s * gaussBinom q s j) * ((-1) ^ u * q ^ (u.choose 2) * gaussBinom q N u *
        (q ^ ((m : ℤ) - n)) ^ u) := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have e1 : N + 1 - 1 - u = N - u := by omega
    have e2 : s - (j + (N - u)) = u := by omega
    simp only [e1, Ek, e2]
    rw [← hN, gb_symm hq (by omega : u ≤ N)]
    have e3 : (((s : ℤ) - ((j + (N - u) : ℕ) : ℤ))) = (u : ℤ) := by
      have : s - (j + (N - u)) = u := e2
      omega
    rw [e3]
    have e4 : ((u : ℤ) * ((m : ℤ) - n) + ((u.choose 2 : ℕ) : ℤ)) =
        (((m : ℤ) - n) * u) + ((u.choose 2 : ℕ) : ℤ) := by ring
    rw [e4, zpow_add₀ hq0, zpow_mul, zpow_natCast, zpow_natCast]
    have e5 : (-1 : ℝ) ^ (j + (N - u)) = (-1) ^ s * (-1) ^ u := by
      have : s + u = (j + (N - u)) + 2 * u := by omega
      calc (-1 : ℝ) ^ (j + (N - u)) = (-1) ^ (j + (N - u)) * ((-1) ^ 2) ^ u := by simp
        _ = (-1) ^ (j + (N - u) + 2 * u) := by rw [← pow_mul, ← pow_add]
        _ = (-1) ^ (s + u) := by rw [this]
        _ = _ := pow_add _ _ _
    rw [e5]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← gauss_neg hq]
  rfl

lemma abInner (hq : 1 < q) (n s m j : ℕ) (hj : j ≤ s) :
    ∑ k ∈ Finset.range (s + 1), ∑ t ∈ Finset.range (s + 1), abTerm q n s m j k t =
      (-1) ^ s * (q ^ ((m : ℤ) * j) * gaussBinom q s j * qPoch (q ^ (-(m : ℤ))) q j *
        qPoch (q ^ ((m : ℤ) - n)) q (s - j)) := by
  have hq0 : q ≠ 0 := by positivity
  have h1 : ∀ k ∈ Finset.range (s + 1), ∑ t ∈ Finset.range (s + 1), abTerm q n s m j k t =
      (q ^ ((m : ℤ) * j) * qPoch (q ^ (-(m : ℤ))) q j) *
        (q ^ (Ek s m n k) * gaussBinom q s k * gaussBinom q k j * (-1) ^ k) := by
    intro k _
    rw [abTerm_t_sum hq n s m j k hj, zpow_add₀ hq0]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Ek_sum hq s m n j hj]
  ring

end ab

theorem solution (q : ℝ) (hq : 1 < q) (n r s m : ℕ) (hs : 0 < s) (hm : s * m = n * r) :
    bSum q n s m = q ^ (n * r) * (-1) ^ s * qPoch (q ^ (-(n : ℤ))) q s := by
  have hq0 : q ≠ 0 := by positivity
  have hc := cor53b hq n r s m hm
  have hnr : q ^ (n * r) * q ^ (-((n : ℤ) * r)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hq0]; push_cast; simp
  unfold bSum
  have h1 : ∀ j ∈ Finset.range (s + 1),
      ∑ k ∈ Finset.range (s + 1), ∑ t ∈ Finset.range (s + 1), abTerm q n s m j k t =
      (-1) ^ s * (q ^ ((j : ℤ) * m) * gaussBinom q s j * qPoch (q ^ (-(m : ℤ))) q j *
        qPoch (q ^ ((m : ℤ) - n)) q (s - j)) := by
    intro j hj
    rw [abInner hq n s m j (by have := Finset.mem_range.mp hj; omega), mul_comm (m : ℤ) j]
  have h2 : ∑ j ∈ Finset.range (s + 1), ∑ k ∈ Finset.range (s + 1), ∑ t ∈ Finset.range (s + 1),
      abTerm q n s m j k t = (-1) ^ s * ∑ j ∈ Finset.range (s + 1),
        (q ^ ((j : ℤ) * m) * gaussBinom q s j * qPoch (q ^ (-(m : ℤ))) q j *
          qPoch (q ^ ((m : ℤ) - n)) q (s - j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl h1
  rw [h2]
  have h3 : ∑ j ∈ Finset.range (s + 1), (q ^ ((j : ℤ) * m) * gaussBinom q s j *
      qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j)) =
      q ^ (n * r) * qPoch (q ^ (-(n : ℤ))) q s := by
    rw [hc, ← mul_assoc, hnr, one_mul]
  rw [h3]; ring
