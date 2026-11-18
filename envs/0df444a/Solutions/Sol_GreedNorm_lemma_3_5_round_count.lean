-- Prove2me | solution 1 for GreedNorm.lemma_3_5_round_count
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-17T14:56:43.419517+00:00
-- url     : https://prove2.me/submissions/8c337691-723b-4fad-aede-aa31fa20626f

import Mathlib

theorem solution (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (r : ℕ → ℕ)
    (h0 : r 0 ≤ n) (hstep : ∀ j, (r (j + 1) : ℝ) ≤ (1 - α) * (r j : ℝ)) :
    (∀ k : ℕ, (n : ℝ) * (1 - α) ^ k < 1 → r k = 0) ∧
      (∀ k : ℕ, 1 ≤ k → 1 / α * Real.log (n : ℝ) ≤ (k : ℝ) → r k = 0) := by
  have hbound : ∀ k : ℕ, (r k : ℝ) ≤ (n : ℝ) * (1 - α) ^ k := by
    intro k
    induction k with
    | zero => simpa using (show (r 0 : ℝ) ≤ (n : ℝ) from by exact_mod_cast h0)
    | succ k ih =>
      have hnonneg : 0 ≤ 1 - α := by linarith
      calc (r (k + 1) : ℝ) ≤ (1 - α) * (r k : ℝ) := hstep k
        _ ≤ (1 - α) * ((n : ℝ) * (1 - α) ^ k) := by
            exact mul_le_mul_of_nonneg_left ih hnonneg
        _ = (n : ℝ) * (1 - α) ^ (k + 1) := by
            rw [pow_succ]
            ring
  constructor
  · intro k hk
    have h1 : (r k : ℝ) < 1 := lt_of_le_of_lt (hbound k) hk
    exact Nat.cast_lt_one.mp h1
  · intro k hk1 hklog
    by_cases hαeq : α = 1
    · subst hαeq
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hle : (r (j + 1) : ℝ) ≤ 0 := by
        simpa using hstep j
      have hzero : (r (j + 1) : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg _)
      exact Nat.cast_eq_zero.mp hzero
    · have hαlt : α < 1 := lt_of_le_of_ne hα1 hαeq
      have hbase : 0 < 1 - α := by linarith
      by_cases hn : n = 0
      · have hle : (r k : ℝ) ≤ 0 := by
          simpa [hn] using hbound k
        have hzero : (r k : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg _)
        exact Nat.cast_eq_zero.mp hzero
      · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
        have hlog : Real.log (1 - α) < -α := by
          have h := Real.log_lt_sub_one_of_pos hbase (by linarith : 1 - α ≠ 1)
          linarith
        have hmul : (k : ℝ) * Real.log (1 - α) < (k : ℝ) * (-α) :=
          mul_lt_mul_of_pos_left hlog hkpos
        have hlog_pow : Real.log ((1 - α) ^ k) < -(α * (k : ℝ)) := by
          rw [Real.log_pow]
          nlinarith [hmul]
        have hpow_pos : 0 < (1 - α) ^ k := pow_pos hbase k
        have hpow_strict : (1 - α) ^ k < Real.exp (-(α * (k : ℝ))) := by
          calc (1 - α) ^ k = Real.exp (Real.log ((1 - α) ^ k)) :=
                (Real.exp_log hpow_pos).symm
            _ < Real.exp (-(α * (k : ℝ))) := Real.exp_lt_exp.mpr hlog_pow
        have hkge' : Real.log (n : ℝ) ≤ α * (k : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hklog hα0.le
          field_simp at h
          linarith
        have hexp : Real.exp (-(α * (k : ℝ))) ≤ 1 / (n : ℝ) := by
          have hR : (1 : ℝ) / (n : ℝ) = Real.exp (-Real.log (n : ℝ)) := by
            rw [Real.exp_neg, Real.exp_log hnpos, inv_eq_one_div]
          rw [hR]
          exact Real.exp_le_exp.mpr (by linarith)
        have hlt : (n : ℝ) * (1 - α) ^ k < 1 := by
          calc (n : ℝ) * (1 - α) ^ k < (n : ℝ) * Real.exp (-(α * (k : ℝ))) :=
                mul_lt_mul_of_pos_left hpow_strict hnpos
            _ ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hexp hnpos.le
            _ = 1 := by field_simp
        have h1 : (r k : ℝ) < 1 := lt_of_le_of_lt (hbound k) hlt
        exact Nat.cast_lt_one.mp h1

