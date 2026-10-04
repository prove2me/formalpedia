-- Prove2me | solution 1 for HardyFiveAxioms.strictMono_completelyMultiplicative_eq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:04:46.818841+00:00
-- url     : https://prove2.me/submissions/afd66388-f70e-4b1c-af6c-6bc4333c14d0

import Mathlib

namespace HardyAux420

lemma K_one (K : ℕ → ℝ)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m < n → K m < K n)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → K (m * n) = K m * K n) : K 1 = 1 := by
  have h11 := hmul 1 1 le_rfl le_rfl
  have h12 := hmul 1 2 le_rfl (by norm_num)
  have hlt := hmono 1 2 le_rfl (by norm_num)
  simp only [one_mul] at h11 h12
  have : K 1 * (K 1 - 1) = 0 := by linarith [h11]
  rcases mul_eq_zero.mp this with h | h
  · exfalso
    rw [h, zero_mul] at h12
    rw [h, h12] at hlt
    exact lt_irrefl _ hlt
  · linarith

lemma K_mono (K : ℕ → ℝ)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m < n → K m < K n) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    K m ≤ K n := by
  rcases lt_or_eq_of_le hmn with h | h
  · exact (hmono m n hm h).le
  · rw [h]

lemma K_pow (K : ℕ → ℝ)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → K (m * n) = K m * K n) (m : ℕ) (hm : 1 ≤ m) :
    ∀ k : ℕ, 1 ≤ k → K (m ^ k) = K m ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp
    · rw [pow_succ, hmul _ _ (Nat.one_le_pow _ _ hm) hm, ih hpos, pow_succ]

end HardyAux420

theorem solution (K : ℕ → ℝ)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m < n → K m < K n)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → K (m * n) = K m * K n) :
    ∃ α : ℝ, 0 < α ∧ ∀ n : ℕ, 1 ≤ n → K n = (n : ℝ) ^ α := by
  have hK1 := HardyAux420.K_one K hmono hmul
  have hK2 : 1 < K 2 := by
    have := hmono 1 2 le_rfl (by norm_num); rw [hK1] at this; exact this
  have hKpos : ∀ n : ℕ, 1 ≤ n → 0 < K n := by
    intro n hn
    have := HardyAux420.K_mono K hmono 1 n le_rfl hn
    rw [hK1] at this; linarith
  set f2 := Real.log (K 2) with hf2
  set g2 := Real.log (2 : ℝ) with hg2
  have hf2pos : 0 < f2 := Real.log_pos hK2
  have hg2pos : 0 < g2 := Real.log_pos (by norm_num)
  refine ⟨f2 / g2, div_pos hf2pos hg2pos, ?_⟩
  intro n hn
  -- key identity: log K n * g2 = log n * f2
  have key : Real.log (K n) * g2 = Real.log (n : ℝ) * f2 := by
    set fn := Real.log (K n)
    set gn := Real.log (n : ℝ)
    have hbound : ∀ k : ℕ, 1 ≤ k →
        (k : ℝ) * |fn * g2 - gn * f2| < f2 * g2 := by
      intro k hk
      set j := Nat.log 2 (n ^ k) with hj
      have hnk : n ^ k ≠ 0 := pow_ne_zero _ (by omega)
      have hlo : 2 ^ j ≤ n ^ k := Nat.pow_log_le_self 2 hnk
      have hhi : n ^ k < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      -- K inequalities
      have hKlo : K (2 ^ j) ≤ K (n ^ k) :=
        HardyAux420.K_mono K hmono _ _ (Nat.one_le_two_pow) hlo
      have hKhi : K (n ^ k) < K (2 ^ (j + 1)) :=
        hmono _ _ (Nat.one_le_pow _ _ hn) hhi
      have hpow2 : ∀ i : ℕ, K (2 ^ i) = K 2 ^ i := by
        intro i
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0; simp [hK1]
        · exact HardyAux420.K_pow K hmul 2 (by norm_num) i hpos
      rw [hpow2, HardyAux420.K_pow K hmul n hn k hk] at hKlo
      rw [hpow2, HardyAux420.K_pow K hmul n hn k hk] at hKhi
      have hKn := hKpos n hn
      have hK2p : 0 < K 2 := by linarith
      have A1 : (j : ℝ) * f2 ≤ k * fn := by
        have := Real.log_le_log (pow_pos hK2p j) hKlo
        rwa [Real.log_pow, Real.log_pow] at this
      have A2 : (k : ℝ) * fn < (j + 1 : ℕ) * f2 := by
        have := Real.log_lt_log (pow_pos hKn k) hKhi
        rwa [Real.log_pow, Real.log_pow] at this
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have B1 : (j : ℝ) * g2 ≤ k * gn := by
        have h := Real.log_le_log (by positivity) (show ((2 ^ j : ℕ) : ℝ) ≤ ((n ^ k : ℕ) : ℝ) by
          exact_mod_cast hlo)
        push_cast at h
        rwa [Real.log_pow, Real.log_pow] at h
      have B2 : (k : ℝ) * gn < (j + 1 : ℕ) * g2 := by
        have h := Real.log_lt_log (by positivity) (show ((n ^ k : ℕ) : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) by
          exact_mod_cast hhi)
        push_cast at h
        rwa [Real.log_pow, Real.log_pow] at h
      push_cast at A2 B2
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [← abs_of_nonneg hk0, ← abs_mul, abs_lt]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right A1 hg2pos.le, mul_lt_mul_of_pos_right B2 hf2pos]
      · nlinarith [mul_lt_mul_of_pos_right A2 hg2pos, mul_le_mul_of_nonneg_right B1 hf2pos.le]
    by_contra hne
    have hd : 0 < |fn * g2 - gn * f2| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk⟩ := exists_nat_gt (f2 * g2 / |fn * g2 - gn * f2|)
    have hk1 : 1 ≤ k := by
      have : (0 : ℝ) < k := lt_trans (div_pos (mul_pos hf2pos hg2pos) hd) hk
      exact_mod_cast this
    have := hbound k hk1
    rw [div_lt_iff₀ hd] at hk
    linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.rpow_def_of_pos hnpos]
  have : Real.log (n : ℝ) * (f2 / g2) = Real.log (K n) := by
    field_simp
    linarith [key]
  rw [this, Real.exp_log (hKpos n hn)]
