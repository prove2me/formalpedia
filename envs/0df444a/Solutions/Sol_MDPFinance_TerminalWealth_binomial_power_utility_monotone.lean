-- Prove2me | solution 1 for MDPFinance.TerminalWealth.binomial_power_utility_monotone
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:03:25.19196+00:00
-- url     : https://prove2.me/submissions/aab69f91-9200-4a09-9592-5fb31682cd3e

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_BinomialPower

open MDPFinance.TerminalWealth

namespace BPUMCex

theorem delta : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num

theorem rp2 (x : ℝ) : x ^ ((1 - (1 / 2 : ℝ))⁻¹) = x ^ 2 := by
  rw [delta, Real.rpow_two]

theorem rp1 (x : ℝ) : x ^ ((1 - (1 / 2 : ℝ))⁻¹ * (1 / 2)) = x := by
  rw [delta, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]

/-- `α^*(p) = -½ (p² - 4(1-p)²) / (p² + 2(1-p)²)` for `i = -2`, `u = 0`, `d = -3`, `γ = ½`. -/
theorem alpha_eq (p : ℝ) : binomialAlphaStar (-2) 0 (-3) (1 / 2) p =
    (-1) / 2 * ((p ^ 2 - 4 * (1 - p) ^ 2) / (p ^ 2 + 2 * (1 - p) ^ 2)) := by
  unfold binomialAlphaStar
  simp only [rp2, rp1]
  norm_num

end BPUMCex

open BPUMCex in
theorem solution : ¬ (∀ (i u down γ : ℝ) (hγ1 : γ < 1) (hγ0 : γ ≠ 0)
    (hdown : down < 1 + i) (hu : 1 + i < u),
    (∀ p ∈ Set.Ioo (0 : ℝ) 1,
        (0 < γ → IsMaxOn (binomialObjective i u down γ p)
          (Set.Icc (binomialAlpha0 i u) (binomialAlpha1 i down)) (binomialAlphaStar i u down γ p)) ∧
        (γ < 0 → IsMinOn (binomialObjective i u down γ p)
          (Set.Ioo (binomialAlpha0 i u) (binomialAlpha1 i down))
          (binomialAlphaStar i u down γ p))) ∧
      MonotoneOn (binomialAlphaStar i u down γ) (Set.Ioo (0 : ℝ) 1) ∧
      binomialAlphaStar i u down γ ((1 + i - down) / (u - down)) = 0) := by
  intro h
  have hm := (h (-2) 0 (-3) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.1
  have := hm (show (1 / 2 : ℝ) ∈ Set.Ioo 0 1 by norm_num) (show (2 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)
    (by norm_num)
  rw [alpha_eq, alpha_eq] at this
  norm_num at this

#print axioms solution
