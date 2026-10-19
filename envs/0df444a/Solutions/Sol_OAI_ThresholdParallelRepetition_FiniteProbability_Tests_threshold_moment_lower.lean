-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.FiniteProbability.Tests.threshold_moment_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:45:57.19752+00:00
-- url     : https://prove2.me/submissions/a48e826b-defd-415b-96d4-ea3f23325635

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

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.FiniteProbability OAI.ThresholdParallelRepetition.FiniteProbability.Tests
universe u_I u_Ω
open scoped BigOperators
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)


theorem solution {q : ℝ} (hq : 0 ≤ q) (t : ℕ) :
    (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t ≤ moment ρ win ∅ t := by
  have hrate : ∀ ω, 0 ≤ rate win ω := fun ω =>
    Law.avg_nonneg _ (fun i => by split_ifs <;> norm_num)
  have hl : (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t =
      ρ.avg (fun ω => (if q ≤ rate win ω then (1:ℝ) else 0)*q^t) := by
    simp only [Law.avg, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [hl, moment]
  apply Law.avg_mono
  intro ω
  have he : event win ∅ ω = 1 := by simp [event]
  rw [he, one_mul]
  split_ifs with h
  · rw [one_mul]; exact pow_le_pow_left₀ hq h t
  · rw [zero_mul]; exact pow_nonneg (hrate ω) t

