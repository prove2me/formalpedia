-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree_slack
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:53:49.919037+00:00
-- url     : https://prove2.me/submissions/e7f0ae16-8154-46ed-a735-1b2089222480

import Mathlib

variable (R : Real)

theorem solution
    (s : Nat) (hs : 0 < s) (B : Nat) (hBR : (B : Real) < (s : Real) * R)
    (L : Nat) (hL : 0 < L) :
    ∃ Q : Nat, ∀ q : Nat, Q ≤ q →
      ((q * B + L : Nat) : Real) < ((s * q : Nat) : Real) * R := by
  have hgap : 0 < (s : ℝ) * R - B := by linarith
  obtain ⟨Q, hQ⟩ := exists_nat_gt ((L : ℝ) / ((s : ℝ) * R - B))
  refine ⟨Q, fun q hq => ?_⟩
  have hq' : (Q : ℝ) ≤ q := by exact_mod_cast hq
  rw [div_lt_iff₀ hgap] at hQ
  push_cast
  nlinarith
