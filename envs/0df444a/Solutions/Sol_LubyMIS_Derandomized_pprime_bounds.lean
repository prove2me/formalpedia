-- Prove2me | solution 1 for LubyMIS.Derandomized.pprime_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:25:51.91073+00:00
-- url     : https://prove2.me/submissions/75754a4c-0bbe-4562-a621-73d70c0248f1

import Mathlib

namespace LubyMIS.Derandomized

theorem aux_ppb_nat (q d : ℕ) (hd : 1 ≤ d) (h16 : 16 * d < q) :
    2 * d * (q / (2 * d)) ≤ q ∧ 4 * q ≤ 9 * d * (q / (2 * d)) := by
  have h2d : 0 < 2 * d := by omega
  have h1 : 2 * d * (q / (2 * d)) ≤ q := Nat.mul_div_le q (2 * d)
  have h2 : q < 2 * d * (q / (2 * d) + 1) := by
    have := Nat.lt_mul_div_succ q h2d
    linarith
  have h3 : 8 ≤ q / (2 * d) := by
    rw [Nat.le_div_iff_mul_le h2d]
    omega
  refine ⟨h1, ?_⟩
  have h4 : 8 * d ≤ d * (q / (2 * d)) := by
    have := Nat.mul_le_mul_left d h3
    linarith
  nlinarith

end LubyMIS.Derandomized

open LubyMIS.Derandomized

theorem solution (n q d : ℕ) (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (hd : 1 ≤ d)
    (h16 : 16 * d < n) :
    8 / 9 * (1 / (2 * (d : ℝ))) ≤ ((q / (2 * d) : ℕ) : ℝ) / q ∧
      ((q / (2 * d) : ℕ) : ℝ) / q ≤ 1 / (2 * (d : ℝ)) := by
  obtain ⟨h1, h2⟩ := aux_ppb_nat q d hd (by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h1' : (2 * (d : ℝ)) * ((q / (2 * d) : ℕ) : ℝ) ≤ q := by exact_mod_cast h1
  have h2' : 4 * (q : ℝ) ≤ 9 * (d : ℝ) * ((q / (2 * d) : ℕ) : ℝ) := by exact_mod_cast h2
  constructor
  · have hL : 8 / 9 * (1 / (2 * (d : ℝ))) = 4 / (9 * (d : ℝ)) := by
      field_simp
      ring
    rw [hL, div_le_div_iff₀ (by positivity) hqpos]
    linarith
  · rw [div_le_div_iff₀ hqpos (by positivity)]
    linarith
