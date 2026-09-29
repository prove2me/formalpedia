-- Prove2me | solution 1 for HolographicQuantumMatter.breitenlohner_freedman_bound
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:23:46.587984+00:00
-- url     : https://prove2.me/submissions/d027c546-2704-4667-8b1a-6d3845af13a4

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (d : ℕ) (msq L : ℝ) :
    (∃ Δ : ℝ, Δ * (Δ - ((d : ℝ) + 1)) = msq * L ^ 2) ↔
      -(((d : ℝ) + 1) ^ 2) / 4 ≤ msq * L ^ 2 := by
  constructor
  · rintro ⟨Δ, hΔ⟩
    nlinarith [sq_nonneg (Δ - ((d : ℝ) + 1) / 2)]
  · intro h
    let r : ℝ := Real.sqrt ((((d : ℝ) + 1) ^ 2) / 4 + msq * L ^ 2)
    have hnonneg : 0 ≤ (((d : ℝ) + 1) ^ 2) / 4 + msq * L ^ 2 := by
      linarith
    have hr : r ^ 2 = (((d : ℝ) + 1) ^ 2) / 4 + msq * L ^ 2 := by
      exact Real.sq_sqrt hnonneg
    refine ⟨((d : ℝ) + 1) / 2 + r, ?_⟩
    nlinarith

#print axioms solution
