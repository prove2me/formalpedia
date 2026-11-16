-- Prove2me | solution 1 for Kyprianou.Ch01.branchingMechanism_expUniformBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:08:35.332598+00:00
-- url     : https://prove2.me/submissions/88e47505-595d-4a08-8788-3ba3c98ce56b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 ≤ b) (k : ℕ) (y : ℝ)
    (hy0 : 0 ≤ y) (hyb : y ≤ b) :
    |1 - Real.exp (-y * ((k : ℝ) - 1))| ≤ 1 + Real.exp b := by
  have hmax : -y * ((k : ℝ) - 1) ≤ b := by
    cases k with
    | zero =>
      simpa using hyb
    | succ n =>
      have hn : (1 : ℝ) ≤ (↑(n + 1) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hm : 0 ≤ y * (((n + 1 : ℕ) : ℝ) - 1) :=
        mul_nonneg hy0 (sub_nonneg.mpr hn)
      linarith
  have hexp : Real.exp (-y * ((k : ℝ) - 1)) ≤ Real.exp b :=
    Real.exp_le_exp.mpr hmax
  calc
    _ ≤ |(1 : ℝ)| + |Real.exp (-y * ((k : ℝ) - 1))| :=
      abs_sub _ _
    _ = 1 + Real.exp (-y * ((k : ℝ) - 1)) := by simp
    _ ≤ 1 + Real.exp b := by linarith
