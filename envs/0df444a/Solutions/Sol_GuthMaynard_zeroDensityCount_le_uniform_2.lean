-- Prove2me | solution 2 for GuthMaynard.zeroDensityCount_le_uniform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:15:25.209871+00:00
-- url     : https://prove2.me/submissions/caa0d5fe-8ad3-4c81-bde4-5e908b888aac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GuthMaynard_zeroDensityCount_le_uniform_interior
import Theorems.Thm_GuthMaynard_huxley_density_estimate_uniform

open Filter Topology
open scoped ENNReal

theorem solution :
    ∃ (C A : ℝ) (e : ℝ → ℝ), Tendsto e atTop (𝓝 0) ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ A) := by
  obtain ⟨C₀, e, he, hmain⟩ := GuthMaynard.zeroDensityCount_le_uniform_interior
  obtain ⟨C₁, hhuxley⟩ := GuthMaynard.huxley_density_estimate_uniform
  let C : ℝ := max 0 (max C₀ C₁)
  let E : ℝ → ℝ := fun T ↦ |e T|
  refine ⟨C, 44, E, ?_, ?_⟩
  · simpa [E] using he.abs
  intro T hT σ hσ
  have hTpos : 0 < T := by linarith
  have hTone : (1 : ℝ) ≤ T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogpow : 0 < Real.log T ^ (44 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hC₀ : C₀ ≤ C := le_max_of_le_right (le_max_left _ _)
  have hC₁ : C₁ ≤ C := le_max_of_le_right (le_max_right _ _)
  have hC : 0 ≤ C := le_max_left _ _
  have hmain' : ∀ τ : ℝ, τ ∈ Set.Icc (1 / 2 : ℝ) (4 / 5 : ℝ) →
      (LindelofHypothesis.zeroDensityCount τ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + E T) * (1 - τ)) * Real.log T ^ (44 : ℝ)) := by
    intro τ hτ
    have hpow : T ^ ((30 / 13 + e T) * (1 - τ)) ≤
        T ^ ((30 / 13 + E T) * (1 - τ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hTone
      have htau : 0 ≤ 1 - τ := by linarith [hτ.2]
      have heE : e T ≤ E T := le_abs_self _
      nlinarith
    have hrpow : 0 ≤ T ^ ((30 / 13 + e T) * (1 - τ)) := (Real.rpow_pos_of_pos hTpos _).le
    have hrpowE : 0 ≤ T ^ ((30 / 13 + E T) * (1 - τ)) := (Real.rpow_pos_of_pos hTpos _).le
    apply (hmain T hT τ hτ).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      C₀ * T ^ ((30 / 13 + e T) * (1 - τ)) * Real.log T ^ (44 : ℝ)
          ≤ C * T ^ ((30 / 13 + e T) * (1 - τ)) * Real.log T ^ (44 : ℝ) := by
          gcongr
      _ ≤ C * T ^ ((30 / 13 + E T) * (1 - τ)) * Real.log T ^ (44 : ℝ) := by
          gcongr
  by_cases hsplit : σ ≤ 4 / 5
  · exact hmain' σ ⟨hσ.1, hsplit⟩
  · have hσlower : 4 / 5 ≤ σ := le_of_not_ge hsplit
    have hσthree : 3 / 4 ≤ σ := by linarith
    have hh := hhuxley T hT σ hσthree hσ.2
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    norm_num [Real.rpow_natCast]
    have hden : (0 : ℝ) < 3 * σ - 1 := by linarith
    have hratio : 3 * (1 - σ) / (3 * σ - 1) ≤ (30 / 13 : ℝ) * (1 - σ) := by
      have hone_sigma : 0 ≤ 1 - σ := by linarith [hσ.2]
      apply (div_le_iff₀ hden).2
      nlinarith
    have hexponent : 3 * (1 - σ) / (3 * σ - 1) ≤ (30 / 13 + E T) * (1 - σ) := by
      have hone_sigma : 0 ≤ 1 - σ := by linarith [hσ.2]
      have hE : 0 ≤ E T := abs_nonneg _
      nlinarith
    have hpow : T ^ (3 * (1 - σ) / (3 * σ - 1)) ≤
        T ^ ((30 / 13 + E T) * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hTone hexponent
    have hrpow : 0 ≤ T ^ (3 * (1 - σ) / (3 * σ - 1)) := (Real.rpow_pos_of_pos hTpos _).le
    calc
      C₁ * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ (44 : ℕ)
          ≤ C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ (44 : ℕ) := by
          gcongr
      _ ≤ C * T ^ ((30 / 13 + E T) * (1 - σ)) * Real.log T ^ (44 : ℕ) := by
          gcongr
