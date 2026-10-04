-- Prove2me | solution 1 for NumberField.Brumer.exists_parameters
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:30:37.197711+00:00
-- url     : https://prove2.me/submissions/74f1c00d-6bda-4b3e-b545-d768c7a1a775

import Mathlib

namespace NumberField.Brumer.ParAux

/-- The real step: `ρ ^ E * X ^ d < 1` from `X ≤ A ^ P`, `ρ ^ m₀ * A < 1` and
`m₀ * (P * d) ≤ E`. -/
lemma step_real (ρ A X : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (m₀ P d E : ℕ)
    (hm : ρ ^ m₀ * A < 1) (hA : 0 ≤ A) (hX0 : 0 ≤ X) (hXP : X ≤ A ^ P) (hD : P * d ≠ 0)
    (hE : m₀ * (P * d) ≤ E) : ρ ^ E * X ^ d < 1 := by
  calc ρ ^ E * X ^ d ≤ ρ ^ (m₀ * (P * d)) * A ^ (P * d) := by
        apply mul_le_mul (pow_le_pow_of_le_one hρ0 hρ1.le hE) _ (by positivity) (by positivity)
        rw [pow_mul]
        exact pow_le_pow_left₀ hX0 hXP d
    _ = (ρ ^ m₀ * A) ^ (P * d) := by rw [mul_pow, pow_mul]
    _ < 1 := pow_lt_one₀ (by positivity) hm hD

/-- The bracket is at most `A ^ P` for an explicit natural number `P`. -/
lemma X_bound (A C₁ C₃ : ℝ) (N n R0 S0 q R1 S1 M : ℕ) (hA : 0 < A) (hC₁ : 0 < C₁)
    (hC₃ : 0 < C₃) (hC₁A : C₁ ≤ A) (hC₃A : C₃ ≤ A) (hN : (N : ℝ) ≤ A ^ M) :
    (N : ℝ) ^ n * ((N : ℝ) ^ n * C₁ ^ (N * R0 + S0) * (N : ℝ) ^ S0) *
        C₃ ^ (q * N * R1 + S1) * (N : ℝ) ^ S1 ≤
      A ^ (M * n + (M * n + (N * R0 + S0) + M * S0) + (q * N * R1 + S1) + M * S1) := by
  calc _ ≤ (A ^ M) ^ n * ((A ^ M) ^ n * A ^ (N * R0 + S0) * (A ^ M) ^ S0) *
        A ^ (q * N * R1 + S1) * (A ^ M) ^ S1 := by gcongr
    _ = _ := by ring

/-- The core natural-number inequality, with `u = t ^ (b + 2)` and `v = t ^ j`. -/
lemma nat_core (K q b n J S1 t u v : ℕ) (h_a : 10 * K * b * n ≤ t) (h_b : 10 * K ≤ t)
    (h_c : 10 * K * J ≤ t) (h_d : 10 * K * b * J ≤ t) (h_e : 10 * K * q ≤ t) (ht : 1 ≤ t)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hS1 : S1 ≤ J * u) :
    K * (b * t * n + (b * t * n + (u + J * u) + b * t * (J * u)) + (q * u * t * v + S1) +
      b * t * S1) ≤ t * t * u * v := by
  have m1 : t * t ≤ t * t * u * v := by
    calc t * t = t * t * 1 * 1 := by ring
      _ ≤ t * t * u * v := by gcongr
  have m2 : t * u ≤ t * t * u * v := by
    calc t * u = 1 * t * u * 1 := by ring
      _ ≤ t * t * u * v := by gcongr
  have m3 : t * t * u ≤ t * t * u * v := by
    calc t * t * u = t * t * u * 1 := by ring
      _ ≤ t * t * u * v := by gcongr
  have e1 : 10 * (K * (b * t * n)) ≤ t * t * u * v := by
    refine le_trans ?_ m1
    calc 10 * (K * (b * t * n)) = (10 * K * b * n) * t := by ring
      _ ≤ t * t := Nat.mul_le_mul_right _ h_a
  have e2 : 10 * (K * u) ≤ t * t * u * v := by
    refine le_trans ?_ m2
    calc 10 * (K * u) = (10 * K) * u := by ring
      _ ≤ t * u := Nat.mul_le_mul_right _ h_b
  have e3 : 10 * (K * (J * u)) ≤ t * t * u * v := by
    refine le_trans ?_ m2
    calc 10 * (K * (J * u)) = (10 * K * J) * u := by ring
      _ ≤ t * u := Nat.mul_le_mul_right _ h_c
  have e4 : 10 * (K * (b * t * (J * u))) ≤ t * t * u * v := by
    refine le_trans ?_ m3
    calc 10 * (K * (b * t * (J * u))) = (10 * K * b * J) * (t * u) := by ring
      _ ≤ t * (t * u) := Nat.mul_le_mul_right _ h_d
      _ = t * t * u := by ring
  have e5 : 10 * (K * (q * u * t * v)) ≤ t * t * u * v := by
    calc 10 * (K * (q * u * t * v)) = (10 * K * q) * (u * t * v) := by ring
      _ ≤ t * (u * t * v) := Nat.mul_le_mul_right _ h_e
      _ = t * t * u * v := by ring
  have e6 : 10 * (K * S1) ≤ t * t * u * v := by
    refine le_trans ?_ e3
    gcongr
  have e7 : 10 * (K * (b * t * S1)) ≤ t * t * u * v := by
    refine le_trans ?_ e4
    gcongr
  nlinarith [e1, e2, e3, e4, e5, e6, e7, Nat.zero_le (t * t * u * v)]

/-- The natural-number inequality for the exponents in step `j`. -/
lemma nat_main (m₀ d q b n J N R0 S0 R1 S1 t j a : ℕ)
    (ht : 10 * (m₀ * d) * (q + 1) * (b + 1) * (n + 1) * (J + 1) ≤ t) (ht1 : 1 ≤ t)
    (ha : a = b + 2) (hN : N = t ^ b) (hR0 : R0 = t ^ 2) (hS0 : S0 = J * t ^ a)
    (hR1 : R1 = t ^ (j + 3)) (hS1 : S1 ≤ J * t ^ a) :
    m₀ * ((b * t * n + (b * t * n + (N * R0 + S0) + b * t * S0) + (q * N * R1 + S1) +
      b * t * S1) * d) ≤ t ^ (j + 2) * t ^ a := by
  subst ha hN hR0 hS0 hR1
  have hu : 1 ≤ t ^ (b + 2) := Nat.one_le_pow _ _ ht1
  have hv : 1 ≤ t ^ j := Nat.one_le_pow _ _ ht1
  have h_a : 10 * (m₀ * d) * b * n ≤ t := by
    have : 10 * (m₀ * d) * 1 * b * n * 1 ≤ 10 * (m₀ * d) * (q + 1) * (b + 1) * (n + 1) * (J + 1) := by
      gcongr <;> omega
    have := le_trans this ht
    simpa using this
  have h_b : 10 * (m₀ * d) ≤ t := by
    have : 10 * (m₀ * d) * 1 * 1 * 1 * 1 ≤ 10 * (m₀ * d) * (q + 1) * (b + 1) * (n + 1) * (J + 1) := by
      gcongr <;> omega
    have := le_trans this ht
    simpa using this
  have h_c : 10 * (m₀ * d) * J ≤ t := by
    have : 10 * (m₀ * d) * 1 * 1 * 1 * J ≤ 10 * (m₀ * d) * (q + 1) * (b + 1) * (n + 1) * (J + 1) := by
      gcongr <;> omega
    have := le_trans this ht
    simpa using this
  have h_d : 10 * (m₀ * d) * b * J ≤ t := by
    have : 10 * (m₀ * d) * 1 * b * 1 * J ≤ 10 * (m₀ * d) * (q + 1) * (b + 1) * (n + 1) * (J + 1) := by
      gcongr <;> omega
    have := le_trans this ht
    simpa using this
  have h_e : 10 * (m₀ * d) * q ≤ t := by
    have : 10 * (m₀ * d) * q * 1 * 1 * 1 ≤ 10 * (m₀ * d) * (q + 1) * (b + 1) * (n + 1) * (J + 1) := by
      gcongr <;> omega
    have := le_trans this ht
    simpa using this
  have key := nat_core (m₀ * d) q b n J S1 t (t ^ (b + 2)) (t ^ j) h_a h_b h_c h_d h_e ht1 hu hv hS1
  calc _ = (m₀ * d) * (b * t * n + (b * t * n + (t ^ (b + 2) + J * t ^ (b + 2)) +
        b * t * (J * t ^ (b + 2))) + (q * t ^ (b + 2) * t * t ^ j + S1) + b * t * S1) := by ring
    _ ≤ t * t * t ^ (b + 2) * t ^ j := key
    _ = _ := by ring

/-- The counting condition. -/
lemma count_ineq (k d J a b t : ℕ) (ht : 2 * d * (J + 1) ^ k ≤ t) (hab : a * k + 3 = b * (k + 1))
    (ht1 : 1 ≤ t) :
    2 * d * (J * t ^ a + 1) ^ k * t ^ 2 ≤ (t ^ b) ^ (k + 1) := by
  have h1 : J * t ^ a + 1 ≤ (J + 1) * t ^ a := by
    have := Nat.one_le_pow a t ht1
    rw [add_mul, one_mul]
    exact Nat.add_le_add_left this _
  calc 2 * d * (J * t ^ a + 1) ^ k * t ^ 2 ≤ 2 * d * ((J + 1) * t ^ a) ^ k * t ^ 2 := by gcongr
    _ = 2 * d * (J + 1) ^ k * t ^ (a * k + 2) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ t * t ^ (a * k + 2) := by gcongr
    _ = t ^ (a * k + 3) := by ring
    _ = (t ^ b) ^ (k + 1) := by rw [hab, pow_mul]

end NumberField.Brumer.ParAux

theorem solution (n d q : ℕ) (hn : 0 < n) (hd : 0 < d) (C₁ C₃ ρ : ℝ)
    (h1 : 1 ≤ C₁) (h3 : 1 ≤ C₃) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ (N J : ℕ) (S R : ℕ → ℕ), 0 < N ∧
      2 * d * (S 0 + 1) ^ (n - 1) * R 0 ≤ N ^ n ∧ N ^ n ≤ R J ∧
      ∀ j < J, S (j + 1) ≤ S j ∧
        ρ ^ (R j * (S j - S (j + 1))) *
          ((N : ℝ) ^ n * ((N : ℝ) ^ n * C₁ ^ (N * R 0 + S 0) * (N : ℝ) ^ S 0) *
            C₃ ^ (q * N * R (j + 1) + S (j + 1)) * (N : ℝ) ^ S (j + 1)) ^ d < 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = max (max C₁ C₃) 2 := ⟨_, rfl⟩
  have hA2 : (2 : ℝ) ≤ A := hAdef ▸ le_max_right _ _
  have hA0 : (0 : ℝ) < A := by linarith
  have hC₁A : C₁ ≤ A := hAdef ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hC₃A : C₃ ≤ A := hAdef ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hC₁0 : 0 < C₁ := by linarith
  have hC₃0 : 0 < C₃ := by linarith
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / A by positivity) hρ1
  have hm : ρ ^ m₀ * A < 1 := by rwa [lt_div_iff₀ hA0] at hm₀
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = 2 * k + 3 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = b + 2 := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = b * (k + 1) := ⟨_, rfl⟩
  obtain ⟨t, ht1, htA, htB⟩ : ∃ t : ℕ, 1 ≤ t ∧
      10 * (m₀ * d) * (q + 1) * (b + 1) * (k + 1 + 1) * (J + 1) ≤ t ∧
      2 * d * (J + 1) ^ k ≤ t :=
    ⟨10 * (m₀ * d) * (q + 1) * (b + 1) * (k + 1 + 1) * (J + 1) + 2 * d * (J + 1) ^ k + 1,
      by omega, by omega, by omega⟩
  have hN : ((t ^ b : ℕ) : ℝ) ≤ A ^ (b * t) := by
    have h2t : (t : ℝ) ≤ A ^ t := by
      have : (t : ℝ) < 2 ^ t := by exact_mod_cast Nat.lt_two_pow_self (n := t)
      exact this.le.trans (pow_le_pow_left₀ (by norm_num) hA2 t)
    push_cast
    calc (t : ℝ) ^ b ≤ (A ^ t) ^ b := pow_le_pow_left₀ (by positivity) h2t b
      _ = A ^ (b * t) := by rw [← pow_mul, mul_comm]
  refine ⟨t ^ b, J, fun j => (J - j) * t ^ a, fun j => t ^ (j + 2),
    pow_pos ht1 _, ?_, ?_, ?_⟩
  · show 2 * d * (J * t ^ a + 1) ^ k * t ^ 2 ≤ (t ^ b) ^ (k + 1)
    exact NumberField.Brumer.ParAux.count_ineq k d J a b t htB (by subst ha hb; ring) ht1
  · show (t ^ b) ^ (k + 1) ≤ t ^ (J + 2)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right ht1 (by omega)
  · intro j hj
    have hdiff : (J - j) * t ^ a - (J - (j + 1)) * t ^ a = t ^ a := by
      have : J - j = (J - (j + 1)) + 1 := by omega
      rw [this, Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
    refine ⟨Nat.mul_le_mul_right _ (by omega), ?_⟩
    show ρ ^ (t ^ (j + 2) * ((J - j) * t ^ a - (J - (j + 1)) * t ^ a)) * _ < 1
    rw [hdiff]
    have hbt : 0 < b * t * (k + 1) := Nat.mul_pos (Nat.mul_pos (by omega) ht1) (by omega)
    refine NumberField.Brumer.ParAux.step_real ρ A _ hρ0 hρ1 m₀ _ d _ hm hA0.le (by positivity)
      (NumberField.Brumer.ParAux.X_bound A C₁ C₃ (t ^ b) (k + 1) (t ^ (0 + 2)) ((J - 0) * t ^ a) q (t ^ (j + 1 + 2))
        ((J - (j + 1)) * t ^ a) (b * t) hA0 hC₁0 hC₃0 hC₁A hC₃A hN) ?_ ?_
    · exact Nat.mul_ne_zero (by omega) (by omega)
    · exact NumberField.Brumer.ParAux.nat_main m₀ d q b (k + 1) J (t ^ b) (t ^ (0 + 2)) ((J - 0) * t ^ a) (t ^ (j + 1 + 2))
        ((J - (j + 1)) * t ^ a) t j a htA ht1 ha rfl (by simp) (by simp) (by ring_nf)
        (Nat.mul_le_mul_right _ (by omega))
