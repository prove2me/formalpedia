-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coeff_mul_norm_le_choose_weighted_succ_general
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:38:59.565553+00:00
-- url     : https://prove2.me/submissions/48412c28-9d9f-4fe2-a0d2-929111678f64

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped BigOperators

theorem solution
    (f g : PowerSeries ℂ) (k n : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hf : ∀ r, ‖PowerSeries.coeff r f‖ ≤
      C ^ k * (Nat.choose (r + k - 1) r : ℝ))
    (hg : ∀ r, ‖PowerSeries.coeff r g‖ ≤ C)
    (hk : 1 ≤ k) :
    ‖PowerSeries.coeff n (f * g)‖ ≤
      C ^ (k + 1) * (Nat.choose (n + (k + 1) - 1) n : ℝ) := by
  have hnat : ∑ r ∈ Finset.range (n + 1), (r + k - 1).choose r =
      (n + k).choose n := by
    calc
      _ = ∑ r ∈ Finset.range (n + 1), (r + (k - 1)).choose (k - 1) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hi : r + k - 1 = r + (k - 1) := by omega
        rw [hi]
        exact Nat.choose_symm_add
      _ = (n + (k - 1) + 1).choose (k - 1 + 1) := Nat.sum_range_add_choose n (k - 1)
      _ = (n + k).choose k := by congr 1 <;> omega
      _ = (n + k).choose n := Nat.choose_symm_of_eq_add (by omega)
  have hsum : ∑ r ∈ Finset.range (n + 1), ((r + k - 1).choose r : ℝ) =
      ((n + k).choose n : ℝ) := by exact_mod_cast hnat
  have hidx : n + (k + 1) - 1 = n + k := by omega
  rw [hidx]
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p : ℕ × ℕ => PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) n]
  calc
    ‖∑ r ∈ Finset.range (n + 1), PowerSeries.coeff r f * PowerSeries.coeff (n - r) g‖
        ≤ ∑ r ∈ Finset.range (n + 1), ‖PowerSeries.coeff r f * PowerSeries.coeff (n - r) g‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range (n + 1), (C ^ k * ((r + k - 1).choose r : ℝ)) * C := by
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul]
      exact mul_le_mul (hf r) (hg (n - r)) (norm_nonneg _)
        (mul_nonneg (pow_nonneg hC _) (Nat.cast_nonneg _))
    _ = C ^ (k + 1) * ∑ r ∈ Finset.range (n + 1), ((r + k - 1).choose r : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [pow_succ]
      ring
    _ = C ^ (k + 1) * ((n + k).choose n : ℝ) := by rw [hsum]

#print axioms solution
