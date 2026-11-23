-- Prove2me | solution 1 for LindelofHypothesis.density_hypothesis_of_lindelof
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:29:05.824969+00:00
-- url     : https://prove2.me/submissions/5676b56f-b0b7-4222-97ce-4156376128b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_LindelofHypothesis_ingham_density_estimate

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis
end LindelofHypothesis
open LindelofHypothesis
theorem solution (hL : RiemannVonMangoldt.LindelofHypothesis)
    (σ : ℝ) (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ T in atTop,
      (zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (C * T ^ (2 * (1 - σ) + ε)) :=
  by
  rcases hσ₀.eq_or_lt with h | h
  · -- σ = 1/2: Ingham's exponent 3 / (2 - 1/2) * (1 - 1/2) + ε equals 2 * (1 - 1/2) + ε
    subst h
    obtain ⟨C, hC⟩ := LindelofHypothesis.ingham_density_estimate (1 / 2) hσ₀ hσ₁ ε hε
    have he : 3 / (2 - (1 / 2 : ℝ)) * (1 - 1 / 2) + ε = 2 * (1 - 1 / 2) + ε := by norm_num
    rw [he] at hC
    exact ⟨C, hC⟩
  · -- σ > 1/2: under the Riemann hypothesis no zero has real part ≥ σ, so the count is 0
    refine ⟨0, Filter.Eventually.of_forall fun T => ?_⟩
    have hempty : IsEmpty {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} := by
      refine ⟨fun x => ?_⟩
      obtain ⟨s, hz, hre, -⟩ := x
      have hhalf : s.re = 1 / 2 := by
        refine mathlib_riemannHypothesis s hz ?_ ?_
        · rintro ⟨n, rfl⟩
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hc : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
          rw [hc] at hre
          linarith
        · rintro rfl
          exact riemannZeta_one_ne_zero hz
      linarith
    have h0 : zeroDensityCount σ T = 0 := by
      rw [zeroDensityCount, tsum_empty]
    rw [h0]
    simp
