-- Prove2me | solution 1 for JRPHard.RangeDiv.gcd_le_half
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T20:01:10.740804+00:00
-- url     : https://prove2.me/submissions/add44457-74d7-4878-aafb-d2dc2e8d0d5a

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting
open JRPHard.RangeDiv

theorem solution(M q : ℕ) (hq : 0 < q) (hne : Nat.gcd q M ≠ q) :
    2 * Nat.gcd q M ≤ q := by
  have hd := Nat.gcd_dvd_left q M
  have hg : 0 < Nat.gcd q M := Nat.gcd_pos_of_pos_left _ hq
  generalize Nat.gcd q M = g at *
  obtain ⟨k, rfl⟩ := hd
  rcases k with _ | _ | k
  · simp at hq
  · simp at hne
  · nlinarith
