-- Prove2me | solution 2 for OAI.ThresholdParallelRepetition.FiniteProbability.Tests.moment_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:46:58.399727+00:00
-- url     : https://prove2.me/submissions/55676f9b-7857-4947-a51a-e415662e4f47

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


theorem solution {r e : ℝ} (hr : 0 ≤ r) (_he : 0 ≤ e) (T : ℕ)
    (hstep : ∀ c : Finset I, c.card < T →
      (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) ≤ r*mass ρ win c+e) :
    ∀ t : ℕ, ∀ c : Finset I, c.card+t ≤ T →
      moment ρ win c t ≤ r^t*mass ρ win c + e*∑ s ∈ Finset.range t, r^s := by
  have hev : ∀ (c : Finset I) i ω, event win c ω * (if win ω i then (1:ℝ) else 0) =
      event win (insert i c) ω := by
    intro c i ω
    simp only [event, Finset.forall_mem_insert]
    by_cases h1 : win ω i = true <;> by_cases h2 : ∀ j ∈ c, win ω j = true <;> simp [h1, h2]
  have hmul : ∀ (a : ℝ) (f : I → ℝ), (uniform (R := I)).avg (fun i => a * f i) =
      a * (uniform (R := I)).avg f := by
    intro a f; simp only [Law.avg, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring
  have key : ∀ (c : Finset I) (t : ℕ), moment ρ win c (t+1) =
      (uniform (R := I)).avg (fun i => moment ρ win (insert i c) t) := by
    intro c t
    simp only [moment]
    symm; rw [Law.avg_comm]
    congr 1; funext ω
    have : (fun i => event win (insert i c) ω * rate win ω ^ t) =
        (fun i => (event win c ω * rate win ω ^ t) * (if win ω i then (1:ℝ) else 0)) := by
      funext i; rw [← hev]; ring
    rw [this, hmul, pow_succ]
    simp only [rate]; ring
  intro t
  induction t with
  | zero => intro c _; simp [moment, mass, Law.avg, event]
  | succ t ih =>
    intro c hc
    rw [key]
    have h1 : (uniform (R := I)).avg (fun i => moment ρ win (insert i c) t) ≤
        (uniform (R := I)).avg (fun i => r^t * mass ρ win (insert i c) + e*∑ s ∈ Finset.range t, r^s) := by
      apply Law.avg_mono; intro i; apply ih
      have := Finset.card_insert_le i c; omega
    have h2 : (uniform (R := I)).avg (fun i => r^t * mass ρ win (insert i c) + e*∑ s ∈ Finset.range t, r^s) =
        r^t * (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) + e*∑ s ∈ Finset.range t, r^s := by
      have hadd : ∀ f g : I → ℝ, (uniform (R := I)).avg (fun i => f i + g i) =
          (uniform (R := I)).avg f + (uniform (R := I)).avg g := by
        intro f g; simp only [Law.avg, smul_add, Finset.sum_add_distrib]
      rw [hadd (fun i => r^t * mass ρ win (insert i c)) (fun _ => e*∑ s ∈ Finset.range t, r^s), hmul,
        Law.avg_const]
    have h3 := hstep c (by omega)
    have hrt : 0 ≤ r^t := pow_nonneg hr t
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h3 hrt]

