-- Prove2me | solution 1 for LevyStochCalc.Poisson.iUnion_timeSlab
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:52:30.699805+00:00
-- url     : https://prove2.me/submissions/670752c6-708f-41da-8535-335364d5cc48

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000

open LevyStochCalc.Poisson

theorem solution (n : ℕ) : (⋃ k : ℕ, timeSlab n k) = Set.Ioi (0 : ℝ) := by
  ext x
  simp only [Set.mem_iUnion, timeSlab, Set.mem_Ioc, Set.mem_Ioi]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  constructor
  · rintro ⟨k, hk1, _⟩
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / 2 ^ n := by positivity
    linarith
  · intro hx
    have hx2 : 0 < x * (2 : ℝ) ^ n := mul_pos hx h2pos
    have hceil_pos : 0 < ⌈x * (2 : ℝ) ^ n⌉₊ := Nat.ceil_pos.mpr hx2
    refine ⟨⌈x * (2 : ℝ) ^ n⌉₊ - 1, ?_, ?_⟩
    · rw [div_lt_iff₀ h2pos]
      have h1 : (⌈x * (2 : ℝ) ^ n⌉₊ - 1 : ℕ) < ⌈x * (2 : ℝ) ^ n⌉₊ := Nat.sub_lt hceil_pos one_pos
      have h2 : ((⌈x * (2 : ℝ) ^ n⌉₊ - 1 : ℕ) : ℝ) < x * (2 : ℝ) ^ n :=
        (Nat.lt_ceil).mp h1
      exact h2
    · rw [le_div_iff₀ h2pos]
      have h3 : x * (2 : ℝ) ^ n ≤ (⌈x * (2 : ℝ) ^ n⌉₊ : ℝ) := Nat.le_ceil _
      have h4 : ((⌈x * (2 : ℝ) ^ n⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈x * (2 : ℝ) ^ n⌉₊ : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hceil_pos
      linarith
