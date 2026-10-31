-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:02:10.713566+00:00
-- url     : https://prove2.me/submissions/941ce7df-4ffe-4d54-919d-b72fd0488aa0

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubexponentialNorm

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat

lemma IA8_toMeasure_eq (lam : ℝ≥0) : (poissonPMF lam).toMeasure = poissonMeasure lam := by
  rw [Measure.ext_iff_singleton]
  intro a
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), poissonMeasure_singleton,
    ← poissonPMFReal_ofReal_eq_poissonPMF]
  rfl

lemma IA8_hasSum (lam : ℝ≥0) (s : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n)!) * Real.exp (n * s))
      (Real.exp (-(lam : ℝ)) * Real.exp ((lam : ℝ) * Real.exp s)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp s)).mul_left
    (Real.exp (-(lam : ℝ)))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : (fun n : ℕ => (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n)!) * Real.exp (n * s)) =
      fun i : ℕ => Real.exp (-(lam : ℝ)) * (((lam : ℝ) * Real.exp s) ^ i / (i)!) := by
    funext n
    rw [Real.exp_nat_mul, mul_pow]
    ring
  rw [e]; exact h

theorem solution (lam : ℝ≥0) :
    HighDimProb.Concentration.subexponentialNorm (poissonPMF lam).toMeasure (fun k : ℕ => (k : ℝ)) ≤
      4 * (lam : ℝ) + 1 := by
  set t : ℝ := 4 * (lam : ℝ) + 1 with ht
  have hl : (0 : ℝ) ≤ lam := lam.2
  have htpos : 0 < t := by positivity
  set s : ℝ := 1 / t with hs
  have hspos : 0 < s := by positivity
  have hs1 : s ≤ 1 := by rw [hs, div_le_one htpos]; linarith
  have hfun : (fun k : ℕ => Real.exp (|(k : ℝ)| / t)) = fun k : ℕ => Real.exp (k * s) := by
    funext k; rw [abs_of_nonneg (Nat.cast_nonneg k), hs, mul_one_div]
  have hHS := IA8_hasSum lam s
  have hint : Integrable (fun k : ℕ => Real.exp (|(k : ℝ)| / t)) (poissonPMF lam).toMeasure := by
    rw [hfun, IA8_toMeasure_eq, integrable_poissonMeasure_iff]
    refine hHS.summable.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hval : ∫ k, Real.exp (|(k : ℝ)| / t) ∂(poissonPMF lam).toMeasure =
      Real.exp (-(lam : ℝ)) * Real.exp ((lam : ℝ) * Real.exp s) := by
    have hint' := hint
    rw [hfun, IA8_toMeasure_eq] at hint' ⊢
    rw [integral_poissonMeasure' hint']
    simpa [smul_eq_mul] using hHS.tsum_eq
  have hbound : Real.exp (-(lam : ℝ)) * Real.exp ((lam : ℝ) * Real.exp s) ≤ 2 := by
    rw [← Real.exp_add]
    have he : Real.exp s ≤ 1 + s + s ^ 2 := by
      have := Real.abs_exp_sub_one_sub_id_le (x := s) (by rw [abs_of_pos hspos]; exact hs1)
      linarith [le_abs_self (Real.exp s - 1 - s)]
    have hls : (lam : ℝ) * s ≤ 1 / 4 := by
      rw [hs, mul_one_div, div_le_iff₀ htpos]; linarith
    have h1 : -(lam : ℝ) + lam * Real.exp s ≤ 1 / 2 := by
      have : (lam : ℝ) * Real.exp s ≤ lam * (1 + s + s ^ 2) := mul_le_mul_of_nonneg_left he hl
      have h2 : (lam : ℝ) * s ^ 2 ≤ lam * s := by
        have : s ^ 2 ≤ s := by nlinarith
        exact mul_le_mul_of_nonneg_left this hl
      nlinarith
    calc Real.exp (-(lam : ℝ) + lam * Real.exp s) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 h1
      _ ≤ 2 := by
        have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
        norm_num at this ⊢; linarith
  unfold HighDimProb.Concentration.subexponentialNorm
  apply csInf_le
  · exact ⟨0, fun x hx => hx.1.le⟩
  · exact ⟨htpos, hint, hval ▸ hbound⟩
