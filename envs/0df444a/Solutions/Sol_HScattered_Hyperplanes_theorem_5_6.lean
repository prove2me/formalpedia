-- Prove2me | solution 1 for HScattered.Hyperplanes.theorem_5_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:15:04.620804+00:00
-- url     : https://prove2.me/submissions/aac6344b-605c-4838-8a02-f48df73966ed

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom

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

section carl
variable {q : ℝ}

lemma compose (u v : ℕ → ℕ → ℂ) (hu : ∀ i j, i < j → u i j = 0) (a b : ℕ → ℂ)
    (ha : ∀ k, a k = ∑ j ∈ Finset.range (k + 1), u k j * b j) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), v k i * a i =
      ∑ j ∈ Finset.range (k + 1), (∑ i ∈ Finset.range (k + 1), v k i * u i j) * b j := by
  have h1 : ∀ i ∈ Finset.range (k + 1), v k i * a i =
      ∑ j ∈ Finset.range (k + 1), v k i * u i j * b j := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [ha i, Finset.mul_sum]
    have hsub : Finset.range (i + 1) ⊆ Finset.range (k + 1) := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    rw [Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl; intro j _; ring
    · intro j _ hj
      have := Finset.mem_range.not.mp hj
      rw [hu i j (by omega)]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

lemma one_pow_eq (hq : 1 < q) (k : ℕ) :
    ((-1 : ℝ) ^ k * q ^ (k.choose 2)) * ((-1 : ℝ) ^ k * q ^ ((k.choose 2 : ℤ) + (1 - (k : ℤ)) * k)) = 1 := by
  have hq0 : q ≠ 0 := by positivity
  have h1 : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by rw [← mul_pow]; simp
  have h2 : q ^ (k.choose 2) * q ^ ((k.choose 2 : ℤ) + (1 - (k : ℤ)) * k) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hq0]
    have h : (((k.choose 2 : ℕ) : ℤ) + (((k.choose 2 : ℕ) : ℤ) + (1 - (k : ℤ)) * k)) = 0 := by
      have : (2 * k.choose 2 + k : ℕ) = k * k := ch2_double k
      have h' : (2 * (k.choose 2 : ℤ) + k : ℤ) = k * k := by exact_mod_cast this
      linarith
    rw [h]; simp
  calc _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (q ^ (k.choose 2) *
        q ^ ((k.choose 2 : ℤ) + (1 - (k : ℤ)) * k)) := by ring
    _ = 1 := by rw [h1, h2]; ring

lemma one_pow_eq2 (hq : 1 < q) (k : ℕ) :
    ((-1 : ℝ) ^ k * q ^ ((k.choose 2 : ℤ) + (k : ℤ))) *
      ((-1 : ℝ) ^ k * q ^ ((k.choose 2 : ℤ) + (-(k : ℤ)) * k)) = 1 := by
  have hq0 : q ≠ 0 := by positivity
  have h1 : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by rw [← mul_pow]; simp
  have h2 : q ^ ((k.choose 2 : ℤ) + (k : ℤ)) *
      q ^ ((k.choose 2 : ℤ) + (-(k : ℤ)) * k) = 1 := by
    rw [← zpow_add₀ hq0]
    have h' : (2 * (k.choose 2 : ℤ) + k : ℤ) = k * k := by exact_mod_cast ch2_double k
    have : ((k.choose 2 : ℤ) + (k : ℤ) + ((k.choose 2 : ℤ) + (-(k : ℤ)) * k)) = 0 := by
      linarith
    rw [this]; simp
  calc _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (q ^ ((k.choose 2 : ℤ) + (k : ℤ)) *
        q ^ ((k.choose 2 : ℤ) + (-(k : ℤ)) * k)) := by ring
    _ = 1 := by rw [h1, h2]; ring

lemma carlitz_fwd (hq : 1 < q) (a b : ℕ → ℂ)
    (ha : ∀ k : ℕ, a k = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (gaussBinom q k j : ℂ) * b j) (k : ℕ) :
    b k = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℂ) ^ j * (q : ℂ) ^ ((j.choose 2 : ℤ) + j - (j : ℤ) * k) *
          (gaussBinom q k j : ℂ) * a j := by
  set u : ℕ → ℕ → ℂ := fun i j => (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (gaussBinom q i j : ℂ)
    with hu
  set v : ℕ → ℕ → ℂ := fun k i => (-1 : ℂ) ^ i * (q : ℂ) ^ ((i.choose 2 : ℤ) + i - (i : ℤ) * k) *
    (gaussBinom q k i : ℂ) with hv
  have hu0 : ∀ i j, i < j → u i j = 0 := by
    intro i j hij; simp [hu, gb_lt hij]
  have hcomp := compose u v hu0 a b (fun k => by rw [ha k]) k
  have hform : ∀ j, (∑ i ∈ Finset.range (k + 1), v k i * u i j) =
      (((-1 : ℝ) ^ j * q ^ (j.choose 2) *
        ∑ i ∈ Finset.range (k + 1), ((-1 : ℝ) ^ i * q ^ ((i.choose 2 : ℤ) + (1 - (k : ℤ)) * i)) *
          gaussBinom q k i * gaussBinom q i j : ℝ) : ℂ) := by
    intro j
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hu, hv]
    have : ((i.choose 2 : ℤ) + i - (i : ℤ) * k) = (i.choose 2 : ℤ) + (1 - (k : ℤ)) * i := by ring
    rw [this]
    ring
  show b k = ∑ i ∈ Finset.range (k + 1), v k i * a i
  rw [hcomp]
  rw [Finset.sum_eq_single k]
  · rw [hform k, orth_diag k hq]
    have := one_pow_eq hq k
    have h2 : (((-1 : ℝ) ^ k * q ^ (k.choose 2) *
        ((-1 : ℝ) ^ k * q ^ ((k.choose 2 : ℤ) + (1 - (k : ℤ)) * k)) : ℝ) : ℂ) = 1 := by
      rw [this]; simp
    rw [h2, one_mul]
  · intro j hj hjk
    have hj' := Finset.mem_range.mp hj
    rw [hform j]
    have : ∑ i ∈ Finset.range (k + 1), ((-1 : ℝ) ^ i * q ^ ((i.choose 2 : ℤ) + (1 - (k : ℤ)) * i)) *
          gaussBinom q k i * gaussBinom q i j = 0 :=
      orth_gen hq j k (by omega) (1 - (k : ℤ)) (by omega) (by omega)
    rw [this]; simp
  · intro h; simp at h

lemma carlitz_bwd (hq : 1 < q) (a b : ℕ → ℂ)
    (hb : ∀ k : ℕ, b k = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℂ) ^ j * (q : ℂ) ^ ((j.choose 2 : ℤ) + j - (j : ℤ) * k) *
          (gaussBinom q k j : ℂ) * a j) (k : ℕ) :
    a k = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (gaussBinom q k j : ℂ) * b j := by
  set u : ℕ → ℕ → ℂ := fun k j => (-1 : ℂ) ^ j * (q : ℂ) ^ ((j.choose 2 : ℤ) + j - (j : ℤ) * k) *
    (gaussBinom q k j : ℂ) with hu
  set v : ℕ → ℕ → ℂ := fun k i => (-1 : ℂ) ^ i * (q : ℂ) ^ (i.choose 2) * (gaussBinom q k i : ℂ)
    with hv
  have hu0 : ∀ i j, i < j → u i j = 0 := by
    intro i j hij; simp [hu, gb_lt hij]
  have hcomp := compose u v hu0 b a (fun k => by rw [hb k]) k
  have hform : ∀ j, (∑ i ∈ Finset.range (k + 1), v k i * u i j) =
      (((-1 : ℝ) ^ j * q ^ ((j.choose 2 : ℤ) + (j : ℤ)) *
        ∑ i ∈ Finset.range (k + 1), ((-1 : ℝ) ^ i * q ^ ((i.choose 2 : ℤ) + (-(j : ℤ)) * i)) *
          gaussBinom q k i * gaussBinom q i j : ℝ) : ℂ) := by
    intro j
    have hq0 : q ≠ 0 := by positivity
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_zpow, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_sum, Complex.ofReal_intCast, Complex.ofReal_natCast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hu, hv]
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    have eL : (q : ℂ) ^ (((j.choose 2 : ℕ) : ℤ) + (j : ℤ) - (j : ℤ) * (i : ℤ)) =
        (q : ℂ) ^ (j.choose 2) * (q : ℂ) ^ (j : ℤ) * (q : ℂ) ^ ((-(j : ℤ)) * (i : ℤ)) := by
      rw [← zpow_natCast, ← zpow_add₀ hqC, ← zpow_add₀ hqC]; congr 1; ring
    have eR : (q : ℂ) ^ (((i.choose 2 : ℕ) : ℤ) + (-(j : ℤ)) * (i : ℤ)) =
        (q : ℂ) ^ (i.choose 2) * (q : ℂ) ^ ((-(j : ℤ)) * (i : ℤ)) := by
      rw [← zpow_natCast, ← zpow_add₀ hqC]
    have eC : (q : ℂ) ^ (((j.choose 2 : ℕ) : ℤ) + (j : ℤ)) = (q : ℂ) ^ (j.choose 2) * (q : ℂ) ^ (j : ℤ) := by
      rw [← zpow_natCast, ← zpow_add₀ hqC]
    rw [eL, eR, eC]
    ring
  show a k = ∑ i ∈ Finset.range (k + 1), v k i * b i
  rw [hcomp]
  rw [Finset.sum_eq_single k]
  · rw [hform k, orth_diag k hq]
    have := one_pow_eq2 hq k
    have h2 : (((-1 : ℝ) ^ k * q ^ ((k.choose 2 : ℤ) + (k : ℤ)) *
        ((-1 : ℝ) ^ k * q ^ ((k.choose 2 : ℤ) + (-(k : ℤ)) * k)) : ℝ) : ℂ) = 1 := by
      rw [this]; simp
    rw [h2, one_mul]
  · intro j hj hjk
    have hj' := Finset.mem_range.mp hj
    rw [hform j]
    have : ∑ i ∈ Finset.range (k + 1), ((-1 : ℝ) ^ i * q ^ ((i.choose 2 : ℤ) + (-(j : ℤ)) * i)) *
          gaussBinom q k i * gaussBinom q i j = 0 :=
      orth_gen hq j k (by omega) (-(j : ℤ)) (by omega) (by omega)
    rw [this]; simp
  · intro h; simp at h

end carl

theorem solution (q : ℝ) (hq : 1 < q) (a b : ℕ → ℂ) :
    (∀ k : ℕ, a k = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (gaussBinom q k j : ℂ) * b j) ↔
      (∀ k : ℕ, b k = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℂ) ^ j * (q : ℂ) ^ ((j.choose 2 : ℤ) + j - (j : ℤ) * k) *
          (gaussBinom q k j : ℂ) * a j) :=
  ⟨fun h k => carlitz_fwd hq a b h k, fun h k => carlitz_bwd hq a b h k⟩
