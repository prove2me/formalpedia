-- Prove2me | solution 1 for HolographicQuantumMatter.mass_dimension_roots
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:25:34.657986+00:00
-- url     : https://prove2.me/submissions/52a5af9e-3343-4e2c-9bf3-db93ffb0235c

import Definitions.Def_HolographicQuantumMatter_ScalarAdS
import Mathlib.Tactic.Linarith

theorem solution (d : ℕ) (msq L : ℝ)
    (hBF : -(((d : ℝ) + 1) ^ 2) / 4 ≤ msq * L ^ 2) (Δ : ℝ) :
    Δ * (Δ - ((d : ℝ) + 1)) = msq * L ^ 2 ↔
      Δ = HolographicQuantumMatter.deltaPlus d msq L ∨
        Δ = HolographicQuantumMatter.deltaMinus d msq L := by
  have hnonneg : 0 ≤ (((d : ℝ) + 1) ^ 2) / 4 + msq * L ^ 2 := by
    linarith
  have hs : (Real.sqrt ((((d : ℝ) + 1) ^ 2) / 4 + msq * L ^ 2)) ^ 2 =
      (((d : ℝ) + 1) ^ 2) / 4 + msq * L ^ 2 := Real.sq_sqrt hnonneg
  unfold HolographicQuantumMatter.deltaPlus HolographicQuantumMatter.deltaMinus
  constructor
  · intro h
    have hp : (Δ - (((d : ℝ) + 1) / 2 +
        Real.sqrt ((((d : ℝ) + 1) ^ 2) / 4 + msq * L ^ 2))) *
        (Δ - (((d : ℝ) + 1) / 2 -
        Real.sqrt ((((d : ℝ) + 1) ^ 2) / 4 + msq * L ^ 2))) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hp with hp | hp
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · rw [h]
      nlinarith [hs]
    · rw [h]
      nlinarith [hs]

#print axioms solution
