-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.testing_parameters_good
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:43:11.648634+00:00
-- url     : https://prove2.me/submissions/0af6400f-f61b-4b7b-9cb2-87bb787cacb5

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData
import Definitions.Def_OAI_Probability_EntangledGames_Refinement
import Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
import Definitions.Def_OAI_Probability_EntangledGames_Rounding
import Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel
import Definitions.Def_OAI_Probability_EntangledGames_TestMoments

open OAI OAI.ThresholdParallelRepetition
universe u_I
theorem h42_tpg {δ k d p : ℝ} {c : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < k) (hd : 1 ≤ d)
    (hc : (c : ℝ) ≤ δ^9*k/((2:ℝ)^90*(1+Real.log d)))
    (hp : Real.exp (-(δ^8*k/(2:ℝ)^83)) ≤ p) :
    (c : ℝ) ≤ δ*k/4 ∧ (c : ℝ) < k ∧
      Real.log (d^c/p)/(k-(c : ℝ)) ≤ δ^8/(2:ℝ)^80 := by
  have hL : 0 ≤ Real.log d := Real.log_nonneg hd
  have hd0 : 0 < d := by linarith
  have hδ8 : δ^9 ≤ δ^8 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
  have hδ8' : δ^8 ≤ δ := by simpa using pow_le_pow_of_le_one hδ.le hδ1 (show 1 ≤ 8 by norm_num)
  have hδ9p : 0 < δ^9 := by positivity
  -- key: c*(1+log d) ≤ δ^9 k / 2^90
  have hc2 : (c:ℝ)*(1+Real.log d) ≤ δ^9*k/(2:ℝ)^90 := by
    have h1 : 0 < (2:ℝ)^90*(1+Real.log d) := by positivity
    rw [le_div_iff₀ h1] at hc
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg c
  have hc3 : (c:ℝ) ≤ δ^9*k/(2:ℝ)^90 := by nlinarith
  have hc4 : (c:ℝ) ≤ δ*k/4 := by
    have : δ^9*k/(2:ℝ)^90 ≤ δ*k/4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_pos hδ hk]
    linarith
  have hc5 : (c:ℝ) < k := by nlinarith
  refine ⟨hc4, hc5, ?_⟩
  have hp0 : 0 < p := lt_of_lt_of_le (Real.exp_pos _) hp
  have hlogp : -(δ^8*k/(2:ℝ)^83) ≤ Real.log p := by
    rw [← Real.log_exp (-(δ^8*k/(2:ℝ)^83))]; exact Real.log_le_log (Real.exp_pos _) hp
  have hlog : Real.log (d^c/p) = c*Real.log d - Real.log p := by
    rw [Real.log_div (by positivity) hp0.ne', Real.log_pow]
  rw [hlog]
  have hkc : 3*k/4 ≤ k - c := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  have hcl : (c:ℝ)*Real.log d ≤ δ^8*k/(2:ℝ)^90 := by nlinarith [mul_nonneg hc0 hL]
  have hpos : 0 ≤ δ^8 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hkc hpos]

theorem solution {δ k d p : ℝ} {c : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < k) (hd : 1 ≤ d)
    (hc : (c : ℝ) ≤ δ^9*k/((2:ℝ)^90*(1+Real.log d)))
    (hp : Real.exp (-(δ^8*k/(2:ℝ)^83)) ≤ p) :
    (c : ℝ) ≤ δ*k/4 ∧ (c : ℝ) < k ∧
      Real.log (d^c/p)/(k-(c : ℝ)) ≤ δ^8/(2:ℝ)^80 := by
  exact h42_tpg hδ hδ1 hk hd hc hp

