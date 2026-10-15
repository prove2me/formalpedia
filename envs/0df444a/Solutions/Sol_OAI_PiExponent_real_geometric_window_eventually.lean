-- Prove2me | solution 1 for OAI.PiExponent.real_geometric_window_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:12:18.156362+00:00
-- url     : https://prove2.me/submissions/5999ec64-ec4d-429b-86b1-e0707169b9dc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem solution (theta b : ℝ) (htheta : 0 < theta) (htheta_one : theta < 1)
    (hb : 0 < b) (hgap : b ^ 2 * theta < 1) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      (b ^ m / 8 + 1) ^ 2 * theta ^ m < 1 := by
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hquarter htheta_one
  refine ⟨M, ?_⟩
  intro m hm
  have hsmall : theta ^ m < 1 / 4 :=
    (pow_le_pow_of_le_one htheta.le htheta_one.le hm).trans_lt hM
  have ht_nonneg : 0 ≤ theta ^ m := pow_nonneg htheta.le m
  have hbase_nonneg : 0 ≤ b ^ 2 * theta :=
    mul_nonneg (sq_nonneg b) htheta.le
  have hbound : (b ^ 2 * theta) ^ m ≤ 1 :=
    pow_le_one₀ hbase_nonneg hgap.le
  have hpow : (b ^ 2) ^ m = (b ^ m) ^ 2 := by
    calc
      (b ^ 2) ^ m = b ^ (2 * m) := (pow_mul b 2 m).symm
      _ = b ^ (m * 2) := by rw [Nat.mul_comm 2 m]
      _ = (b ^ m) ^ 2 := pow_mul b m 2
  rw [mul_pow, hpow] at hbound
  have hsquare : (b ^ m / 8 + 1) ^ 2 ≤ (b ^ m) ^ 2 / 32 + 2 := by
    nlinarith only [sq_nonneg (b ^ m / 8 - 1)]
  calc
    (b ^ m / 8 + 1) ^ 2 * theta ^ m ≤
        ((b ^ m) ^ 2 / 32 + 2) * theta ^ m :=
      mul_le_mul_of_nonneg_right hsquare ht_nonneg
    _ = ((b ^ m) ^ 2 * theta ^ m) / 32 + 2 * theta ^ m := by ring
    _ < 1 := by linarith only [hbound, hsmall]
