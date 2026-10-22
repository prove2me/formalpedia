-- Prove2me | solution 1 for LogMeanVar.Complete.theorem_2_ii_range
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:28:16.147994+00:00
-- url     : https://prove2.me/submissions/bc79eab4-4732-4d33-a084-d97935d13f90

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
open LogMeanVar.Complete

theorem solution (M : Market) (hM : M.Standing) (hμr : M.μ ≠ M.r) :
    M.r < aHat M ∧ aHat M < M.r + theta M ^ 2 / 2 := by
  obtain ⟨hσ, hγ, -⟩ := hM
  have hθ : 0 < theta M ^ 2 := by
    unfold theta
    have : (M.μ - M.r) / M.σ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hμr) hσ.ne'
    positivity
  set x := 1 / (1 + M.γ) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
  have e : aHat M = M.r + (x - 1 / 2 * x ^ 2) * theta M ^ 2 := by
    unfold aHat; rw [hx, div_pow, one_pow]
  rw [e]
  constructor
  · have : 0 < x - 1 / 2 * x ^ 2 := by nlinarith
    nlinarith
  · have : x - 1 / 2 * x ^ 2 < 1 / 2 := by nlinarith [sq_nonneg (x - 1)]
    nlinarith
