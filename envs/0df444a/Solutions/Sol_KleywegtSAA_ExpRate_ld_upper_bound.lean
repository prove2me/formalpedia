-- Prove2me | solution 1 for KleywegtSAA.ExpRate.ld_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:57:13.011033+00:00
-- url     : https://prove2.me/submissions/83488e96-beb8-4108-a78c-00cc29f5b3f6

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open KleywegtSAA.ExpRate

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hYm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) P P) :
    ∀ N : ℕ, 1 ≤ N → ∀ a : ℝ,
      ((1 / (N : ℝ) : ℝ) : EReal) * ENNReal.log (P {ω | a ≤ sampleMean Y N ω}) ≤
        - rateFn P (Y 0) a := by
  intro N hN a
  rw [EReal.le_neg]
  unfold rateFn
  refine iSup₂_le (fun t ht => ?_)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hp : P {ω | a ≤ sampleMean Y N ω} = 0
  · rw [hp, ENNReal.log_zero, EReal.coe_mul_bot_of_pos (by positivity), EReal.neg_bot]
    exact le_top
  by_cases hM : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Y 0 ω)) ∂P = ⊤
  · simp only [BellWilliams2001.ThresholdPolicy.logMGF, hM, ENNReal.log_top, EReal.sub_top]
    exact bot_le
  have hInt0 : Integrable (fun ω => Real.exp (t * Y 0 ω)) P := by
    refine ⟨((hYm 0).const_mul t).exp.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact lt_top_iff_ne_top.2 hM
  have hInt : ∀ i, Integrable (fun ω => Real.exp (t * Y i ω)) P := fun i =>
    ((hid i).comp ((measurable_const_mul t).exp)).integrable_iff.2 hInt0
  have hm : 0 < mgf (Y 0) P t := mgf_pos hInt0
  have hlint : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Y 0 ω)) ∂P =
      ENNReal.ofReal (mgf (Y 0) P t) := by
    rw [mgf, ofReal_integral_eq_lintegral_ofReal hInt0
      (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  have hΛ : BellWilliams2001.ThresholdPolicy.logMGF P (Y 0) t =
      ((Real.log (mgf (Y 0) P t) : ℝ) : EReal) := by
    simp only [BellWilliams2001.ThresholdPolicy.logMGF]
    rw [hlint, ENNReal.log_ofReal_of_pos hm]
  have hsum := iIndepFun.integrable_exp_mul_sum hind hYm (s := Finset.range N) (t := t)
    (fun i _ => hInt i)
  have hch := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ Finset.range N, Y i) ((N : ℝ) * a) ht hsum
  rw [mgf_sum_of_identDistrib hYm hind (fun i _ j _ => (hid i).trans (hid j).symm) (j := 0)
    (Finset.mem_range.2 hN) t, Finset.card_range] at hch
  have hset : {ω | a ≤ sampleMean Y N ω} =
      {ω | (N : ℝ) * a ≤ (∑ i ∈ Finset.range N, Y i) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sampleMean, Finset.sum_apply]
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hNpos, mul_comm]
  rw [← hset] at hch
  have hpr : (P {ω | a ≤ sampleMean Y N ω}).toReal ≤
      Real.exp (-t * ((N : ℝ) * a)) * mgf (Y 0) P t ^ N := hch
  have hpne : P {ω | a ≤ sampleMean Y N ω} ≠ ⊤ := measure_ne_top _ _
  have hppos : 0 < (P {ω | a ≤ sampleMean Y N ω}).toReal := ENNReal.toReal_pos hp hpne
  rw [hΛ, ← ENNReal.ofReal_toReal hpne, ENNReal.log_ofReal_of_pos hppos]
  rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_neg, EReal.coe_le_coe_iff]
  have hl := Real.log_le_log hppos hpr
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hm N).ne', Real.log_exp, Real.log_pow] at hl
  have h2 := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))
  have h3 : 1 / (N : ℝ) * (-t * ((N : ℝ) * a) + (N : ℝ) * Real.log (mgf (Y 0) P t)) =
      -(t * a) + Real.log (mgf (Y 0) P t) := by
    field_simp
  rw [h3] at h2
  linarith
