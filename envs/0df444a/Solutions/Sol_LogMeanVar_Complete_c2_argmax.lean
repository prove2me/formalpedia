-- Prove2me | solution 1 for LogMeanVar.Complete.c2_argmax
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:28:15.336015+00:00
-- url     : https://prove2.me/submissions/f9cf63b5-cea0-4067-8a5e-f2656e46b1e3

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
open LogMeanVar.Complete

theorem solution (M : Market) (hM : M.Standing) :
    IsMaxOn (fun v : ℝ => v * (M.μ - M.r) - (1 + M.γ) / 2 * v ^ 2 * M.σ ^ 2) Set.univ
        (piHat M) ∧
      ∀ v : ℝ, (v * (M.μ - M.r) - (1 + M.γ) / 2 * v ^ 2 * M.σ ^ 2 =
          piHat M * (M.μ - M.r) - (1 + M.γ) / 2 * piHat M ^ 2 * M.σ ^ 2) → v = piHat M := by
  obtain ⟨hσ, hγ, -⟩ := hM
  have hk : 0 < (1 + M.γ) * M.σ ^ 2 := by positivity
  -- key identity: f(π̂) - f(v) = (1+γ)σ²/2 (v - π̂)²
  have key : ∀ v : ℝ, (piHat M * (M.μ - M.r) - (1 + M.γ) / 2 * piHat M ^ 2 * M.σ ^ 2) -
      (v * (M.μ - M.r) - (1 + M.γ) / 2 * v ^ 2 * M.σ ^ 2) =
      (1 + M.γ) * M.σ ^ 2 / 2 * (v - piHat M) ^ 2 := by
    intro v
    have hp : piHat M * ((1 + M.γ) * M.σ ^ 2) = M.μ - M.r := by
      unfold piHat; field_simp
    have : M.μ - M.r = piHat M * ((1 + M.γ) * M.σ ^ 2) := hp.symm
    rw [this]; ring
  refine ⟨fun v _ => ?_, fun v hv => ?_⟩
  · simp only [Set.mem_setOf_eq]
    have := key v
    nlinarith [sq_nonneg (v - piHat M)]
  · have h0 := key v
    rw [hv, sub_self] at h0
    have : (v - piHat M) ^ 2 = 0 := by
      have h2 : (1 + M.γ) * M.σ ^ 2 / 2 ≠ 0 := by positivity
      exact (mul_eq_zero.mp h0.symm).resolve_left h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
