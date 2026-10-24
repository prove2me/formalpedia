-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.rational_degree_integer_multiple
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:53:52.040884+00:00
-- url     : https://prove2.me/submissions/e5809580-388f-4cc9-a317-38d2e15e1a81

import Mathlib

theorem solution
    (s : Nat) (q : Rat) (R : Real) (B : Nat)
    (hs : 0 < s) (hB : (B : Real) < (s : Real) * R)
    (hq : 0 < q) (hqB : (q : Real) ≤ (B : Real)) :
    ∃ m D : Nat, 0 < m ∧ 0 < D ∧
      q * (m : Rat) = (D : Rat) ∧
      (D : Real) < ((s * m : Nat) : Real) * R := by
  refine ⟨q.den, q.num.toNat, q.den_pos, ?_, ?_, ?_⟩
  · have := Rat.num_pos.mpr hq; omega
  · have h1 : (0:ℤ) ≤ q.num := (Rat.num_pos.mpr hq).le
    have : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg h1
    rw [this]; exact Rat.mul_den_eq_num q
  · have h1 : (0:ℤ) ≤ q.num := (Rat.num_pos.mpr hq).le
    have hD : ((q.num.toNat : ℕ) : ℝ) = (q : ℝ) * q.den := by
      have : ((q.num.toNat : ℕ) : ℚ) = q * q.den := by
        have : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg h1
        rw [this, Rat.mul_den_eq_num]
      exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) this
    rw [hD]
    have hden : (0:ℝ) < q.den := by exact_mod_cast q.den_pos
    push_cast
    have : (q : ℝ) < s * R := lt_of_le_of_lt hqB hB
    nlinarith
