-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.analytic_threshold_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:45:17.982985+00:00
-- url     : https://prove2.me/submissions/dd461e0a-d158-4545-97d7-6a5d81cd15a1

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
import Definitions.Def_OAI_Probability_EntangledGames_TestExtraction

open OAI OAI.ThresholdParallelRepetition
theorem h42_atb {v δ θ R E q : ℝ}
    (hv : 0 ≤ v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : v+δ ≤ 1)
    (hθ : 2 ≤ θ) (hδθ : 8 ≤ δ*θ)
    (hθR : θ/δ ≤ R/4) (hR : 2/δ ≤ R/4) (hE : E ≤ δ*θ/8)
    (hq : q*(v+δ)^(⌊θ⌋₊) ≤ (v+δ/2)^(⌊θ⌋₊)+Real.exp (-R)*(2/δ)) :
    q ≤ Real.exp (-E) := by
  set n := ⌊θ⌋₊ with hn
  have hw : 0 < v+δ := by linarith
  have hwn : 0 < (v+δ)^n := pow_pos hw n
  have hnle : (n:ℝ) ≤ θ := Nat.floor_le (by linarith)
  have hnlt : θ < (n:ℝ) + 1 := Nat.lt_floor_add_one θ
  -- q ≤ a + b
  have hq2 : q ≤ ((v+δ/2)/(v+δ))^n + Real.exp (-R)*(2/δ)/(v+δ)^n := by
    rw [div_pow, ← add_div, le_div_iff₀ hwn]; exact hq
  -- first term
  have hA : ((v+δ/2)/(v+δ))^n ≤ Real.exp (-(δ*θ/4)) := by
    have hb : (v+δ/2)/(v+δ) ≤ 1 - δ/2 := by
      rw [div_le_iff₀ hw]; nlinarith
    have hb0 : 0 ≤ (v+δ/2)/(v+δ) := by positivity
    have h1 : ((v+δ/2)/(v+δ))^n ≤ (Real.exp (-(δ/2)))^n := by
      apply pow_le_pow_left₀ hb0
      have := Real.add_one_le_exp (-(δ/2)); linarith
    rw [← Real.exp_nat_mul] at h1
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  -- second term
  have hB : Real.exp (-R)*(2/δ)/(v+δ)^n ≤ 2*Real.exp (-(5*R/8)) := by
    have hdn : δ^n ≤ (v+δ)^n := pow_le_pow_left₀ hδ.le (by linarith) n
    have hδn : 0 < δ^n := pow_pos hδ n
    have h1 : Real.exp (-R)*(2/δ)/(v+δ)^n ≤ Real.exp (-R)*(2/δ)/δ^n :=
      div_le_div_of_nonneg_left (by positivity) hδn hdn
    have h2 : Real.exp (-R)*(2/δ)/δ^n = 2*Real.exp (-R)*(1/δ)^(n+1) := by
      rw [one_div, inv_pow, pow_succ]; field_simp
    have h3 : (1/δ)^(n+1) ≤ Real.exp ((n+1)/δ) := by
      have hx : 1/δ ≤ Real.exp (1/δ) := by have := Real.add_one_le_exp (1/δ); linarith
      calc (1/δ)^(n+1) ≤ (Real.exp (1/δ))^(n+1) := pow_le_pow_left₀ (by positivity) hx _
        _ = Real.exp ((n+1)/δ) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h4 : ((n:ℝ)+1)/δ ≤ 3*R/8 := by
      have : ((n:ℝ)+1)/δ ≤ θ/δ + 1/δ := by
        rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hδ.le
      have : 1/δ ≤ R/8 := by have : 2/δ = 2*(1/δ) := by ring
                             linarith
      linarith
    calc Real.exp (-R)*(2/δ)/(v+δ)^n ≤ 2*Real.exp (-R)*(1/δ)^(n+1) := h1.trans h2.le
      _ ≤ 2*Real.exp (-R)*Real.exp ((n+1)/δ) := by gcongr
      _ ≤ 2*Real.exp (-R)*Real.exp (3*R/8) := by gcongr
      _ = 2*Real.exp (-(5*R/8)) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  -- final
  set x := δ*θ/8 with hx
  have hx1 : 1 ≤ x := by linarith
  have hRx : 32*x ≤ R := by
    have : δ*θ ≤ θ/δ := by rw [le_div_iff₀ hδ]; nlinarith
    linarith
  have hfin : Real.exp (-(2*x)) + 2*Real.exp (-(20*x)) ≤ Real.exp (-x) := by
    have e1 : Real.exp (-(2*x)) = Real.exp (-x) * Real.exp (-x) := by rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(20*x)) = Real.exp (-x) * Real.exp (-(19*x)) := by rw [← Real.exp_add]; ring_nf
    have k1 : Real.exp (-x) ≤ 1/2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp x; linarith
    have k2 : Real.exp (-(19*x)) ≤ 1/20 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp (19*x); linarith
    rw [e1, e2]; have := Real.exp_pos (-x); nlinarith
  have hA' : Real.exp (-(δ*θ/4)) = Real.exp (-(2*x)) := by rw [hx]; ring_nf
  have hB' : Real.exp (-(5*R/8)) ≤ Real.exp (-(20*x)) := Real.exp_le_exp.mpr (by linarith)
  calc q ≤ _ := hq2
    _ ≤ Real.exp (-(2*x)) + 2*Real.exp (-(20*x)) := by rw [← hA']; linarith
    _ ≤ Real.exp (-x) := hfin
    _ ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith)

theorem solution {v δ θ R E q : ℝ}
    (hv : 0 ≤ v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : v+δ ≤ 1)
    (hθ : 2 ≤ θ) (hδθ : 8 ≤ δ*θ)
    (hθR : θ/δ ≤ R/4) (hR : 2/δ ≤ R/4) (hE : E ≤ δ*θ/8)
    (hq : q*(v+δ)^(⌊θ⌋₊) ≤ (v+δ/2)^(⌊θ⌋₊)+Real.exp (-R)*(2/δ)) :
    q ≤ Real.exp (-E) := by
  exact h42_atb hv hδ hδ1 hs hθ hδθ hθR hR hE hq

