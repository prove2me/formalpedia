-- Prove2me | solution 1 for HScattered.Hyperplanes.quantityA_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:19:23.376817+00:00
-- url     : https://prove2.me/submissions/6e9c640f-1e95-4e0a-bc33-652d6a430ecb

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_qPoch
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

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

section gbs
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

end gbs

section qa
variable {q : ℝ}

lemma hom_gauss (hq : 1 < q) (x y : ℝ) (hx : x ≠ 0) (s : ℕ) :
    ∏ l ∈ Finset.range s, (x - y * q ^ l) =
      ∑ t ∈ Finset.range (s + 1),
        (-1) ^ t * q ^ (t.choose 2) * gaussBinom q s t * y ^ t * x ^ (s - t) := by
  have h1 : ∏ l ∈ Finset.range s, (x - y * q ^ l) =
      ∏ l ∈ Finset.range s, (x * (1 - (y / x) * q ^ l)) := by
    apply Finset.prod_congr rfl; intro l _; field_simp
  rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, gauss_neg hq,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ s := by have := Finset.mem_range.mp ht; omega
  have : x ^ s = x ^ (s - t) * x ^ t := by rw [← pow_add]; congr 1; omega
  rw [this, div_pow]
  field_simp

lemma gb_sw (hq : 1 < q) (s j t : ℕ) :
    gaussBinom q s t * gaussBinom q (s - t) j = gaussBinom q s j * gaussBinom q (s - j) t := by
  by_cases h : j + t ≤ s
  · have h1 := gb_mul hq (k := s) (i := s - t) (j := j) (by omega) (by omega)
    have h2 : gaussBinom q s (s - t) = gaussBinom q s t := gb_symm hq (by omega)
    have h3 : gaussBinom q (s - j) (s - t - j) = gaussBinom q (s - j) t := by
      have := gb_symm hq (n := s - j) (k := t) (by omega)
      rw [← this]; congr 1; omega
    rw [h2, h3] at h1; exact h1
  · have hL : gaussBinom q s t * gaussBinom q (s - t) j = 0 := by
      rcases lt_or_ge s t with h1 | h1
      · rw [gb_lt h1]; ring
      · rw [gb_lt (by omega : s - t < j)]; ring
    have hR : gaussBinom q s j * gaussBinom q (s - j) t = 0 := by
      rcases lt_or_ge s j with h1 | h1
      · rw [gb_lt h1]; ring
      · rw [gb_lt (by omega : s - j < t)]; ring
    rw [hL, hR]

lemma pure_id (hq : 1 < q) (n m r s : ℕ) (hm : s * m = n * r) (hnm : n ≤ m) (hsr : s ≤ r) :
    ∑ t ∈ Finset.range (s + 1), (-1) ^ t * q ^ (t.choose 2) * (q ^ (m - n)) ^ t *
      gaussBinom q s t *
      ∑ j ∈ Finset.range (s - t + 1), gaussBinom q (s - t) j *
        ((∏ l ∈ Finset.range j, (q ^ m - q ^ l)) * (q ^ ((r - j) * n) - 1)) = 0 := by
  have hq0 : q ≠ 0 := by positivity
  set B : ℕ → ℝ := fun j => (∏ l ∈ Finset.range j, (q ^ m - q ^ l)) * (q ^ ((r - j) * n) - 1)
    with hB
  -- extend inner ranges
  have h1 : ∀ t ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s - t + 1),
      gaussBinom q (s - t) j * B j = ∑ j ∈ Finset.range (s + 1), gaussBinom q (s - t) j * B j := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    · intro j _ hj
      have := Finset.mem_range.not.mp hj
      rw [gb_lt (by omega : s - t < j), zero_mul]
  rw [Finset.sum_congr rfl (fun t ht => by rw [h1 t ht])]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- inner sum over t for fixed j
  have h2 : ∀ j ∈ Finset.range (s + 1),
      ∑ t ∈ Finset.range (s + 1), (-1) ^ t * q ^ (t.choose 2) * (q ^ (m - n)) ^ t *
        gaussBinom q s t * (gaussBinom q (s - t) j * B j) =
      B j * gaussBinom q s j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e1 : ∀ t ∈ Finset.range (s + 1),
        (-1) ^ t * q ^ (t.choose 2) * (q ^ (m - n)) ^ t * gaussBinom q s t *
          (gaussBinom q (s - t) j * B j) =
        (B j * gaussBinom q s j) * ((-1) ^ t * q ^ (t.choose 2) * gaussBinom q (s - j) t *
          (q ^ (m - n)) ^ t) := by
      intro t _
      have := gb_sw hq s j t
      calc _ = (-1) ^ t * q ^ (t.choose 2) * (q ^ (m - n)) ^ t * B j *
            (gaussBinom q s t * gaussBinom q (s - t) j) := by ring
        _ = _ := by rw [this]; ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ∑ t ∈ Finset.range (s + 1), (-1) ^ t * q ^ (t.choose 2) * gaussBinom q (s - j) t *
        (q ^ (m - n)) ^ t = ∏ l ∈ Finset.range (s - j), (1 - q ^ (m - n) * q ^ l) := by
      rw [gauss_neg hq]
      symm
      apply Finset.sum_subset
      · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
      · intro t _ ht
        have := Finset.mem_range.not.mp ht
        rw [gb_lt (by omega : s - j < t)]; ring
    rw [e2]
    unfold qPoch
    congr 1
    apply Finset.prod_congr rfl
    intro l _
    have : q ^ ((m : ℤ) - n) = q ^ (m - n) := by
      rw [← zpow_natCast]; congr 1; push_cast [Nat.cast_sub hnm]; ring
    rw [this]
  rw [Finset.sum_congr rfl h2]
  -- now convert B j
  have h3 : ∀ j ∈ Finset.range (s + 1),
      B j * gaussBinom q s j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) =
      q ^ (n * r) * (q ^ ((j : ℤ) * ((m : ℤ) - n)) * gaussBinom q s j *
          qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j)) -
        (q ^ ((j : ℤ) * m) * gaussBinom q s j *
          qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hm1 : q ^ m * q ^ (-(m : ℤ)) = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hq0]; simp
    have hP : ∏ l ∈ Finset.range j, (q ^ m - q ^ l) =
        q ^ ((j : ℤ) * m) * qPoch (q ^ (-(m : ℤ))) q j := by
      have e : ∀ l ∈ Finset.range j, q ^ m - q ^ l = q ^ m * (1 - q ^ (-(m : ℤ)) * q ^ l) := by
        intro l _
        rw [mul_sub, mul_one, ← mul_assoc, hm1, one_mul]
      rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      unfold qPoch
      congr 1
      rw [mul_comm, zpow_mul]; simp
    have e3 : q ^ ((j : ℤ) * m) * q ^ ((r - j) * n) = q ^ (n * r) * q ^ ((j : ℤ) * ((m : ℤ) - n)) := by
      rw [← zpow_natCast q ((r - j) * n), ← zpow_natCast q (n * r), ← zpow_add₀ hq0,
        ← zpow_add₀ hq0]
      congr 1
      push_cast [Nat.cast_sub (show j ≤ r by omega)]
      ring
    simp only [hB]
    rw [hP]
    linear_combination (qPoch (q ^ (-(m : ℤ))) q j * gaussBinom q s j *
      qPoch (q ^ ((m : ℤ) - n)) q (s - j)) * e3
  rw [Finset.sum_congr rfl h3, Finset.sum_sub_distrib, ← Finset.mul_sum, ← cor53a hq n r s m hm]
  have hc := cor53b hq n r s m hm
  have hnr : q ^ (n * r) * q ^ (-((n : ℤ) * r)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hq0]; push_cast; simp
  have : ∑ j ∈ Finset.range (s + 1), q ^ ((j : ℤ) * m) * gaussBinom q s j *
      qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) =
      q ^ (n * r) * qPoch (q ^ (-(n : ℤ))) q s := by
    rw [hc, ← mul_assoc, hnr, one_mul]
  rw [this]; ring

end qa

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

lemma hyp_count (K V : Type*) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hr : 0 < Module.finrank K V) :
    Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} *
        (Nat.card K - 1) = Nat.card K ^ Module.finrank K V - 1 := by
  have e : {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} ≃
      Projectivization K (Module.Dual K V) :=
    (Equiv.subtypeEquiv ((Subspace.orderIsoFiniteDimensional (K := K) (V := V)).toEquiv.trans
        OrderDual.ofDual) (p := fun W : Submodule K V => Module.finrank K W = Module.finrank K V - 1)
      (q := fun Φ : Submodule K (Module.Dual K V) => Module.finrank K Φ = 1) (by
        intro W
        have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
        show _ ↔ Module.finrank K W.dualAnnihilator = 1
        omega)).trans (Projectivization.equivSubmodule K (Module.Dual K V)).symm
  rw [Nat.card_congr e]
  have h1 := Projectivization.card K (Module.Dual K V)
  have h2 : Nat.card (Module.Dual K V) = Nat.card K ^ Module.finrank K V := by
    rw [Module.natCard_eq_pow_finrank (K := K), Subspace.dual_finrank_eq]
  rw [h2] at h1
  exact h1.symm

lemma sum_hCount {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V] (U : Submodule F V) :
    ∑ i ∈ Finset.range (Module.finrank F U + 1), HScattered.Hyperplanes.hCount F K U i =
      Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} := by
  classical
  haveI : Module.Finite F K := Module.Finite.of_finite
  haveI : Module.Finite F V := Module.Finite.trans K V
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (Submodule K V) :=
    Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype (Submodule K V) := Fintype.ofFinite _
  set g : Submodule K V → ℕ := fun W => Module.finrank F ↥(W.restrictScalars F ⊓ U) with hg
  set Hs : Finset (Submodule K V) :=
    Finset.univ.filter (fun W => Module.finrank K W = Module.finrank K V - 1) with hHs
  have hcard : Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} =
      Hs.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfib : ∀ i, HScattered.Hyperplanes.hCount F K U i = (Hs.filter (fun W => g W = i)).card := by
    intro i
    unfold HScattered.Hyperplanes.hCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext W
    simp [hHs, hg]
  rw [hcard, Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.range (Module.finrank F U + 1))]
  · exact Finset.sum_congr rfl (fun i _ => hfib i)
  · intro W _
    simp only [Finset.coe_range, Set.mem_Iio, hg]
    have : Module.finrank F ↥(W.restrictScalars F ⊓ U) ≤ Module.finrank F U :=
      Submodule.finrank_mono inf_le_right
    omega

lemma proj_count (K E : Type*) [Field K] [Finite K] [AddCommGroup E] [Module K E]
    (T : Submodule K E) [Module.Finite K T] :
    Nat.card {Φ : Submodule K E // Module.finrank K Φ = 1 ∧ Φ ≤ T} * (Nat.card K - 1) =
      Nat.card K ^ Module.finrank K T - 1 := by
  have e : Projectivization K T ≃ {Φ : Submodule K E // Module.finrank K Φ = 1 ∧ Φ ≤ T} :=
    (Projectivization.equivSubmodule K T).trans
      { toFun := fun Ψ => ⟨Ψ.1.map T.subtype, by
          refine ⟨?_, Submodule.map_subtype_le T Ψ.1⟩
          exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective T.subtype
            T.injective_subtype Ψ.1)).symm.trans Ψ.2⟩
        invFun := fun Φ => ⟨Φ.1.comap T.subtype, by
          exact (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe Φ.2.2)).trans Φ.2.1⟩
        left_inv := fun Ψ => Subtype.ext (Submodule.comap_map_eq_of_injective T.injective_subtype _)
        right_inv := fun Φ => Subtype.ext (by
          show Submodule.map T.subtype (Submodule.comap T.subtype Φ.1) = Φ.1
          rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr Φ.2.2) }
  rw [← Nat.card_congr e]
  have h1 := Projectivization.card K T
  have h2 : Nat.card T = Nat.card K ^ Module.finrank K T := Module.natCard_eq_pow_finrank (K := K)
  rw [h2] at h1
  exact h1.symm

lemma hyp_count_ge (K V : Type*) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) (hr : Module.finrank K S ≤ Module.finrank K V)
    (hS : 0 < Module.finrank K V) :
    Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1 ∧ S ≤ W} *
        (Nat.card K - 1) = Nat.card K ^ (Module.finrank K V - Module.finrank K S) - 1 := by
  have e : {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1 ∧ S ≤ W} ≃
      {Φ : Submodule K (Module.Dual K V) // Module.finrank K Φ = 1 ∧ Φ ≤ S.dualAnnihilator} :=
    Equiv.subtypeEquiv ((Subspace.orderIsoFiniteDimensional (K := K) (V := V)).toEquiv.trans
        OrderDual.ofDual) (by
      intro W
      have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
      have h2 : (Subspace.orderIsoFiniteDimensional (K := K) (V := V)).toEquiv.trans
          OrderDual.ofDual W = W.dualAnnihilator := rfl
      rw [h2, Subspace.dualAnnihilator_le_dualAnnihilator_iff]
      constructor
      · rintro ⟨h1, h3⟩; exact ⟨by omega, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨by omega, h3⟩)
  rw [Nat.card_congr e]
  have := proj_count K (Module.Dual K V) S.dualAnnihilator
  have hf : Module.finrank K S.dualAnnihilator = Module.finrank K V - Module.finrank K S := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq S
    omega
  rw [hf] at this
  exact this

lemma finrank_sup_span_single {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M] (A : Submodule R M) (v : M) (hv : v ∉ A) :
    Module.finrank R ↥(A ⊔ Submodule.span R {v}) = Module.finrank R A + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ A.zero_mem)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span R {v})
  have h2 : A ⊓ Submodule.span R {v} = ⊥ :=
    disjoint_iff.mp ((Submodule.disjoint_span_singleton' hv0).mpr hv)
  rw [h2, finrank_bot, finrank_span_singleton hv0] at h1
  omega

lemma scat_down {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U) (S : Submodule K V)
    (hSh : Module.finrank K S ≤ h) :
    Module.finrank F ↥(S.restrictScalars F ⊓ U) ≤ Module.finrank K S := by
  have : Module.Finite F K := Module.Finite.of_finite
  have : Module.Finite F V := Module.Finite.trans K V
  obtain ⟨_, hr, hspan, hsc⟩ := hU
  have step : ∀ S : Submodule K V, Module.finrank K S < h →
      Module.finrank K S + 1 ≤ Module.finrank F ↥(S.restrictScalars F ⊓ U) →
      ∃ S2 : Submodule K V, Module.finrank K S2 = Module.finrank K S + 1 ∧
        Module.finrank K S2 + 1 ≤ Module.finrank F ↥(S2.restrictScalars F ⊓ U) := by
    intro S hS hSU
    have hne : ¬ (U : Set V) ⊆ (S : Set V) := by
      intro hsub
      have : Submodule.span K (U : Set V) ≤ S := Submodule.span_le.mpr hsub
      rw [hspan] at this
      have h' : S = ⊤ := top_le_iff.mp this
      have : Module.finrank K S = Module.finrank K V := by rw [h']; simp
      omega
    obtain ⟨v, hvU, hvS⟩ := Set.not_subset.mp hne
    refine ⟨S ⊔ Submodule.span K {v}, ?_, ?_⟩
    · exact finrank_sup_span_single S v hvS
    · rw [finrank_sup_span_single S v hvS]
      have hvA : v ∉ S.restrictScalars F ⊓ U := fun hm => hvS hm.1
      have h1 := finrank_sup_span_single (R := F) (S.restrictScalars F ⊓ U) v hvA
      have hle : (S.restrictScalars F ⊓ U) ⊔ Submodule.span F {v} ≤
          (S ⊔ Submodule.span K {v}).restrictScalars F ⊓ U := by
        apply sup_le
        · exact inf_le_inf_right _ (Submodule.restrictScalars_mono F le_sup_left)
        · rw [Submodule.span_singleton_le_iff_mem]
          exact ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self v), hvU⟩
      have := Submodule.finrank_mono hle
      omega
  have key : ∀ m : ℕ, ∀ S : Submodule K V, Module.finrank K S + m = h →
      Module.finrank K S + 1 ≤ Module.finrank F ↥(S.restrictScalars F ⊓ U) → False := by
    intro m
    induction m with
    | zero =>
      intro S hS hSU
      have := hsc S (by omega)
      omega
    | succ m ih =>
      intro S hS hSU
      obtain ⟨S2, h1, h2⟩ := step S (by omega) hSU
      exact ih S2 (by omega) h2
  by_contra hcon
  exact key (h - Module.finrank K S) S (by omega) (by omega)

lemma span_dim {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U) (k : ℕ) (hk : k ≤ h)
    (u : Fin (k + 1) → V) (hli : LinearIndependent F u) (hu : ∀ j, u j ∈ U) :
    Module.finrank K ↥(Submodule.span K (Set.range u)) = k + 1 := by
  have : Module.Finite F K := Module.Finite.of_finite
  have : Module.Finite F V := Module.Finite.trans K V
  have h1 : Module.finrank K ↥(Submodule.span K (Set.range u)) ≤ k + 1 := by
    have := finrank_range_le_card (R := K) u
    rw [Fintype.card_fin] at this
    exact this
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  set S := Submodule.span K (Set.range u) with hS
  have h2 := scat_down h U hU S (by omega)
  have hmem : ∀ j, u j ∈ S.restrictScalars F ⊓ U := fun j =>
    ⟨Submodule.subset_span ⟨j, rfl⟩, hu j⟩
  let s : Fin (k + 1) → ↥(S.restrictScalars F ⊓ U) := fun j => ⟨u j, hmem j⟩
  have hs : LinearIndependent F s :=
    LinearIndependent.of_comp (S.restrictScalars F ⊓ U).subtype hli
  have := hs.fintype_card_le_finrank
  simp at this
  omega

lemma LIcount {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Finite V]
    (E : Submodule F V) (m : ℕ) :
    ((Nat.card {s : Fin m → E // LinearIndependent F s} : ℕ) : ℤ) =
      ∏ j ∈ Finset.range m, ((Fintype.card F : ℤ) ^ Module.finrank F E - (Fintype.card F : ℤ) ^ j) := by
  by_cases hm : m ≤ Module.finrank F E
  · rw [card_linearIndependent (K := F) (V := E) hm]
    push_cast
    rw [← Fin.prod_univ_eq_prod_range (fun j => ((Fintype.card F : ℤ) ^ Module.finrank F E -
      (Fintype.card F : ℤ) ^ j)) m]
    apply Finset.prod_congr rfl
    intro j _
    have : Fintype.card F ^ (j : ℕ) ≤ Fintype.card F ^ Module.finrank F E :=
      Nat.pow_le_pow_right Fintype.card_pos (by omega)
    rw [Nat.cast_sub this]; push_cast; rfl
  · have hz : Nat.card {s : Fin m → E // LinearIndependent F s} = 0 := by
      rw [Nat.card_eq_zero]; left
      constructor
      rintro ⟨s, hs⟩
      have := hs.fintype_card_le_finrank
      simp at this
      omega
    rw [hz]
    symm
    simp only [Nat.cast_zero]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : Module.finrank F E < m))
    exact sub_self _

lemma card_LI_sub {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Finite V]
    [Fintype V] (E : Submodule F V) (m : ℕ) [DecidablePred (fun u : Fin m → V =>
      LinearIndependent F u ∧ ∀ j, u j ∈ E)] [Fintype (Fin m → V)] :
    ((Finset.univ.filter (fun u : Fin m → V => LinearIndependent F u ∧ ∀ j, u j ∈ E)).card : ℤ) =
      ∏ j ∈ Finset.range m, ((Fintype.card F : ℤ) ^ Module.finrank F E - (Fintype.card F : ℤ) ^ j) := by
  rw [← LIcount E m]
  congr 1
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact
    { toFun := fun u => ⟨fun j => ⟨u.1 j, u.2.2 j⟩,
        LinearIndependent.of_comp E.subtype (by exact u.2.1)⟩
      invFun := fun s => ⟨fun j => (s.1 j : V), by
        refine ⟨?_, fun j => (s.1 j).2⟩
        exact s.2.map' E.subtype (Submodule.ker_subtype E), ⟩
      left_inv := fun u => rfl
      right_inv := fun s => rfl }

set_option maxHeartbeats 2000000 in
lemma lem57 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (k : ℕ) (hk : k < h + 1) :
    ∑ i ∈ Finset.range (Module.finrank F U + 1),
        (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) *
          ∏ j ∈ Finset.range (k + 1), ((Fintype.card F : ℤ) ^ i - (Fintype.card F : ℤ) ^ j) =
      (∏ j ∈ Finset.range (k + 1),
          ((Fintype.card F : ℤ) ^ Module.finrank F U - (Fintype.card F : ℤ) ^ j)) *
        ((Fintype.card F : ℤ) ^ ((Module.finrank K V - k - 1) * Module.finrank F K) - 1) := by
  classical
  have hr : 0 < Module.finrank K V := by have := hU.2.1; omega
  haveI : Module.Finite F K := Module.Finite.of_finite
  haveI : Module.Finite F V := Module.Finite.trans K V
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite (Submodule K V) :=
    Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype (Submodule K V) := Fintype.ofFinite _
  set qq : ℤ := (Fintype.card F : ℤ) with hqq
  set r := Module.finrank K V with hrdef
  set n := Module.finrank F K with hn
  set g : Submodule K V → ℕ := fun W => Module.finrank F ↥(W.restrictScalars F ⊓ U) with hg
  set Hs : Finset (Submodule K V) :=
    Finset.univ.filter (fun W => Module.finrank K W = r - 1) with hHs
  set LIU : Finset (Fin (k + 1) → V) :=
    Finset.univ.filter (fun u => LinearIndependent F u ∧ ∀ j, u j ∈ U) with hLIU
  set cW : Submodule K V → Finset (Fin (k + 1) → V) :=
    fun W => LIU.filter (fun u => ∀ j, u j ∈ W) with hcW
  -- Claim A
  have hA : ∀ W : Submodule K V, ((cW W).card : ℤ) =
      ∏ j ∈ Finset.range (k + 1), (qq ^ (g W) - qq ^ j) := by
    intro W
    rw [← card_LI_sub (W.restrictScalars F ⊓ U) (k + 1)]
    congr 2
    ext u
    simp only [hcW, hLIU, Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_inf,
      Submodule.restrictScalars_mem, forall_and]
    tauto
  -- Claim C
  have hC : ∑ i ∈ Finset.range (Module.finrank F U + 1),
      (hCount F K U i : ℤ) * ∏ j ∈ Finset.range (k + 1), (qq ^ i - qq ^ j) =
      ∑ W ∈ Hs, ∏ j ∈ Finset.range (k + 1), (qq ^ (g W) - qq ^ j) := by
    have hmaps : ∀ W ∈ Hs, g W ∈ Finset.range (Module.finrank F U + 1) := by
      intro W _
      have : Module.finrank F ↥(W.restrictScalars F ⊓ U) ≤ Module.finrank F U :=
        Submodule.finrank_mono inf_le_right
      simp only [Finset.mem_range, hg]; omega
    rw [← Finset.sum_fiberwise_of_maps_to (s := Hs) (g := g)
      (t := Finset.range (Module.finrank F U + 1)) hmaps]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_congr rfl (fun W hW => by rw [(Finset.mem_filter.mp hW).2]), Finset.sum_const,
      nsmul_eq_mul]
    congr 2
    unfold HScattered.Hyperplanes.hCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext W
    simp only [hHs, hg, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  -- Claim B
  have hKc : Nat.card K = Fintype.card F ^ n := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := K)]
  have hB : ∀ u ∈ LIU, ((Hs.filter (fun W => ∀ j, u j ∈ W)).card : ℤ) * (qq ^ n - 1) =
      qq ^ (n * (r - (k + 1))) - 1 := by
    intro u hu
    obtain ⟨hli, huU⟩ := (Finset.mem_filter.mp hu).2
    have hspan := span_dim h U hU k (by omega) u hli huU
    set S := Submodule.span K (Set.range u) with hS
    have hle : Module.finrank K S ≤ r := Submodule.finrank_le S
    have h1 := hyp_count_ge K V S hle hr
    have hcard : Nat.card {W : Submodule K V // Module.finrank K W = r - 1 ∧ S ≤ W} =
        (Hs.filter (fun W => ∀ j, u j ∈ W)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hHs, Finset.filter_filter]
      congr 1
      ext W
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS, Submodule.span_le,
        Set.range_subset_iff]
      exact Iff.rfl
    rw [hcard, hspan, hKc, ← hrdef] at h1
    have h4 : 1 ≤ Fintype.card F ^ n := Nat.one_le_pow _ _ Fintype.card_pos
    have h5 : 1 ≤ (Fintype.card F ^ n) ^ (r - (k + 1)) := Nat.one_le_pow _ _ h4
    have h6 := congrArg (fun m : ℕ => (m : ℤ)) h1
    simp only [Nat.cast_mul, Nat.cast_sub h4, Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at h6
    rw [h6, ← pow_mul]
  -- double counting
  have hD : ∑ W ∈ Hs, (cW W).card = ∑ u ∈ LIU, (Hs.filter (fun W => ∀ j, u j ∈ W)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Hs) (t := LIU)
      (fun (W : Submodule K V) (u : Fin (k + 1) → V) => ∀ j, u j ∈ W)
  have hL : (LIU.card : ℤ) =
      ∏ j ∈ Finset.range (k + 1), (qq ^ (Module.finrank F U) - qq ^ j) := card_LI_sub U (k + 1)
  have hsum : (∑ i ∈ Finset.range (Module.finrank F U + 1),
      (hCount F K U i : ℤ) * (qq ^ n - 1) * ∏ j ∈ Finset.range (k + 1), (qq ^ i - qq ^ j)) =
      (qq ^ n - 1) * ∑ W ∈ Hs, ((cW W).card : ℤ) := by
    calc _ = (qq ^ n - 1) * ∑ i ∈ Finset.range (Module.finrank F U + 1),
          (hCount F K U i : ℤ) * ∏ j ∈ Finset.range (k + 1), (qq ^ i - qq ^ j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = (qq ^ n - 1) * ∑ W ∈ Hs, ∏ j ∈ Finset.range (k + 1), (qq ^ (g W) - qq ^ j) := by
          rw [hC]
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl (fun W _ => (hA W).symm)
  have hfin : (qq ^ n - 1) * ∑ W ∈ Hs, ((cW W).card : ℤ) =
      (LIU.card : ℤ) * (qq ^ (n * (r - (k + 1))) - 1) := by
    rw [← Nat.cast_sum, hD, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun u hu => by rw [mul_comm, hB u hu]), Finset.sum_const,
      nsmul_eq_mul]
  have hexp : (r - k - 1) * n = n * (r - (k + 1)) := by rw [Nat.sub_sub, mul_comm]
  -- reassemble the goal
  have e1 : ∀ i ∈ Finset.range (Module.finrank F U + 1),
      (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) *
          ∏ j ∈ Finset.range (k + 1), ((Fintype.card F : ℤ) ^ i - (Fintype.card F : ℤ) ^ j) =
      (hCount F K U i : ℤ) * (qq ^ n - 1) * ∏ j ∈ Finset.range (k + 1), (qq ^ i - qq ^ j) :=
    fun i _ => rfl
  rw [Finset.sum_congr rfl e1, hsum, hfin, hL, hexp, mul_comm]

lemma eq23 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K) :
    ∑ i ∈ Finset.range (Module.finrank F U + 1),
        (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) =
      (Fintype.card F : ℤ) ^ (Module.finrank K V * Module.finrank F K) - 1 := by
  have hr : 0 < Module.finrank K V := by have := hU.2.1; omega
  have h1 := hyp_count K V hr
  have h2 := sum_hCount (F := F) (K := K) U
  have hK : Nat.card K = Fintype.card F ^ Module.finrank F K := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := K)]
  rw [← Finset.sum_mul, ← Nat.cast_sum, h2]
  have h3 : (Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1} : ℤ) *
      ((Nat.card K : ℤ) - 1) = (Nat.card K : ℤ) ^ Module.finrank K V - 1 := by
    have h4 : 1 ≤ Nat.card K := Nat.card_pos
    have h5 : 1 ≤ Nat.card K ^ Module.finrank K V := Nat.one_le_pow _ _ h4
    have := congrArg (fun n : ℕ => (n : ℤ)) h1
    simp only [Nat.cast_mul, Nat.cast_sub h4, Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at this
    exact this
  rw [hK] at h3
  push_cast at h3
  rw [h3, ← pow_mul, mul_comm (Module.finrank F K)]

lemma eq24 {F K V : Type*} [Field F] [Field K] [Algebra F K]
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

lemma hyp_inter_lb {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (U : Submodule F V) (W : Submodule K V)
    (hW : Module.finrank K W = Module.finrank K V - 1) (hr : 0 < Module.finrank K V) :
    Module.finrank F U ≤ Module.finrank F ↥(W.restrictScalars F ⊓ U) + Module.finrank F K := by
  have : Module.Finite F K := Module.Finite.of_finite
  have : Module.Finite F V := Module.Finite.trans K V
  have h1 : Module.finrank F V = Module.finrank K V * Module.finrank F K :=
    by rw [← Module.finrank_mul_finrank F K V, mul_comm]
  have h2 : Module.finrank F ↥(W.restrictScalars F) = Module.finrank K W * Module.finrank F K := by
    have h2' : Module.finrank F ↥(W.restrictScalars F) = Module.finrank F ↥W := rfl
    rw [h2', ← Module.finrank_mul_finrank F K W, mul_comm]
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (W.restrictScalars F) U
  have h4 : Module.finrank F ↥(W.restrictScalars F ⊔ U) ≤ Module.finrank F V :=
    Submodule.finrank_le _
  have h5 : Module.finrank K V * Module.finrank F K =
      Module.finrank K W * Module.finrank F K + Module.finrank F K := by
    rw [hW]
    obtain ⟨r, hr'⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    rw [hr']; simp [Nat.succ_mul]
  omega


theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K) :
    quantityA F K h U = 0 := by
  have hq : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by positivity
  have hhr := hU.2.1
  have hsr : h + 1 ≤ Module.finrank K V := hhr
  have hm : (h + 1) * Module.finrank F U = Module.finrank F K * Module.finrank K V := by
    rw [hdim, mul_comm]
  have hnm : Module.finrank F K ≤ Module.finrank F U := by
    by_contra hlt
    push_neg at hlt
    have h1 : (h + 1) * Module.finrank F U < (h + 1) * Module.finrank F K :=
      Nat.mul_lt_mul_of_pos_left hlt (by omega)
    have h2 : Module.finrank F K * (h + 1) ≤ Module.finrank F K * Module.finrank K V :=
      Nat.mul_le_mul_left _ hsr
    nlinarith
  have hα := eq24 h U hU hdim
  have hβ0 := eq23 h U hU hdim
  have hβ := lem57 h U hU hdim
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set mm := Module.finrank F U with hmm
  set n := Module.finrank F K with hn
  set r := Module.finrank K V with hr
  -- β_j in closed form
  have hbeta : ∀ j, j ≤ h + 1 → (betaSum F K U j : ℝ) =
      (∏ l ∈ Finset.range j, (q ^ mm - q ^ l)) * (q ^ ((r - j) * n) - 1) := by
    intro j hj
    rcases j with _ | j
    · have := hβ0
      have h' : (betaSum F K U 0 : ℝ) = (q : ℝ) ^ (r * n) - 1 := by
        have : betaSum F K U 0 = (Fintype.card F : ℤ) ^ (r * n) - 1 := by
          rw [← this]; unfold betaSum; simp; try rfl
        rw [this]; push_cast; rfl
      rw [h']; simp
    · have := hβ j (by omega)
      have h' : (betaSum F K U (j + 1) : ℝ) =
          ((∏ l ∈ Finset.range (j + 1), ((Fintype.card F : ℤ) ^ mm - (Fintype.card F : ℤ) ^ l)) *
            ((Fintype.card F : ℤ) ^ ((r - j - 1) * n) - 1) : ℤ) := by
        rw [← this]; rfl
      rw [h']; push_cast
      have e : r - j - 1 = r - (j + 1) := by omega
      rw [e]
  -- the sum A in real form
  set c : ℕ → ℝ := fun i => (hCount F K U i : ℝ) * (q ^ n - 1) with hc
  have hcast : ((quantityA F K h U : ℤ) : ℝ) = ∑ i ∈ Finset.range (mm + 1), c i *
      ∏ l ∈ Finset.range (h + 1), (q ^ i - q ^ (mm - n) * q ^ l) := by
    unfold quantityA
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    simp only [hc, pow_add]
    try rfl
  have hexp : ∀ i, c i * ∏ l ∈ Finset.range (h + 1), (q ^ i - q ^ (mm - n) * q ^ l) =
      ∑ t ∈ Finset.range (h + 1 + 1), ((-1) ^ t * q ^ (t.choose 2) * (q ^ (mm - n)) ^ t *
        gaussBinom q (h + 1) t) * (c i * (q ^ i) ^ (h + 1 - t)) := by
    intro i
    rw [hom_gauss hq (q ^ i) (q ^ (mm - n)) (pow_ne_zero _ hq0) (h + 1), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hα' : ∀ k, k ≤ h + 1 → ∑ i ∈ Finset.range (mm + 1), c i * (q ^ i) ^ k =
      ∑ j ∈ Finset.range (k + 1), gaussBinom q k j *
        ((∏ l ∈ Finset.range j, (q ^ mm - q ^ l)) * (q ^ ((r - j) * n) - 1)) := by
    intro k hk
    have := hα k hk
    have e1 : ∑ i ∈ Finset.range (mm + 1), c i * (q ^ i) ^ k = (alphaSum F K U k : ℝ) := by
      unfold alphaSum
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      simp only [hc, ← pow_mul, mul_comm i k]
      try rfl
    rw [e1, this]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbeta j (by have := Finset.mem_range.mp hj; omega)]
  have hA0 : ((quantityA F K h U : ℤ) : ℝ) = 0 := by
    rw [hcast, Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_comm]
    have e2 : ∀ t ∈ Finset.range (h + 1 + 1),
        ∑ i ∈ Finset.range (mm + 1), ((-1) ^ t * q ^ (t.choose 2) * (q ^ (mm - n)) ^ t *
          gaussBinom q (h + 1) t) * (c i * (q ^ i) ^ (h + 1 - t)) =
        (-1) ^ t * q ^ (t.choose 2) * (q ^ (mm - n)) ^ t * gaussBinom q (h + 1) t *
          ∑ j ∈ Finset.range (h + 1 - t + 1), gaussBinom q (h + 1 - t) j *
            ((∏ l ∈ Finset.range j, (q ^ mm - q ^ l)) * (q ^ ((r - j) * n) - 1)) := by
      intro t ht
      rw [← Finset.mul_sum, hα' (h + 1 - t) (by omega)]
    rw [Finset.sum_congr rfl e2]
    exact pure_id hq n mm r (h + 1) (by rw [hm]) hnm hsr
  exact_mod_cast hA0
