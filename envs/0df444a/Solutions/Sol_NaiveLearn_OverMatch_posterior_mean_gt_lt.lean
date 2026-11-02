-- Prove2me | solution 1 for NaiveLearn.OverMatch.posterior_mean_gt_lt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:43:01.026581+00:00
-- url     : https://prove2.me/submissions/cd8ba177-6466-4d94-8346-5f0972dce3f8

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology
open NaiveLearn.OverMatch

theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1] (hF : F0 ≠ F1) :
    p < ∫ s, posterior p F0 F1 s ∂F1 ∧ ∫ s, posterior p F0 F1 s ∂F0 < p := by
  set a : ENNReal := ENNReal.ofReal p with ha
  set b : ENNReal := ENNReal.ofReal (1 - p) with hb
  set ν : Measure S := a • F1 + b • F0 with hν
  set x : S → ℝ := posterior p F0 F1 with hx
  have hxdef : ∀ s, x s = ((a • F1).rnDeriv ν s).toReal := fun s => rfl
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbt : b ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : a ≠ 0 := by simp [ha, hp0]
  have haR : a.toReal = p := ENNReal.toReal_ofReal hp0.le
  have hbR : b.toReal = 1 - p := ENNReal.toReal_ofReal (by linarith)
  have : IsFiniteMeasure (a • F1) := by
    constructor; rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hat.lt_top
  have : IsFiniteMeasure (b • F0) := by
    constructor; rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hbt.lt_top
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hac : a • F1 ≪ ν := Measure.AbsolutelyContinuous.add_right
    Measure.AbsolutelyContinuous.rfl _
  have hle : a • F1 ≤ ν := Measure.le_add_right le_rfl
  have hle1 : ∀ᵐ s ∂ν, (a • F1).rnDeriv ν s ≤ 1 := Measure.rnDeriv_le_one_of_le hle
  have hxm : Measurable x := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hxb : ∀ᵐ s ∂ν, ‖x s‖ ≤ 1 := by
    filter_upwards [hle1] with s hs
    rw [hxdef, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hs
  have hxi : Integrable x ν := Integrable.of_bound hxm.aestronglyMeasurable 1 hxb
  have hxxi : Integrable (fun s => x s * x s) ν := by
    refine Integrable.of_bound (hxm.mul hxm).aestronglyMeasurable 1 ?_
    filter_upwards [hxb] with s hs
    rw [norm_mul]; nlinarith [norm_nonneg (x s)]
  have hle_b : b • F0 ≤ ν := Measure.le_add_left le_rfl
  have hxi1 : Integrable x (a • F1) := hxi.mono_measure hle
  have hxi0 : Integrable x (b • F0) := hxi.mono_measure hle_b
  -- E1
  have E1 : ∫ s, x s * x s ∂ν = p * ∫ s, x s ∂F1 := by
    have := integral_toReal_rnDeriv_mul hac (f := x)
    rw [integral_smul_measure, haR, smul_eq_mul] at this
    simpa [hxdef] using this
  -- E2
  have E2 : ∫ s, x s ∂ν = p := by
    have := integral_toReal_rnDeriv_mul hac (f := fun _ => (1 : ℝ))
    simp only [mul_one, integral_const, smul_eq_mul] at this
    have h2 : ∫ s, x s ∂ν = ∫ s, ((a • F1).rnDeriv ν s).toReal ∂ν := rfl
    rw [h2, this]
    simp [Measure.real, Measure.smul_apply, haR]
  -- E3
  have E3 : ∫ s, x s ∂ν = p * ∫ s, x s ∂F1 + (1 - p) * ∫ s, x s ∂F0 := by
    rw [hν, integral_add_measure hxi1 hxi0, integral_smul_measure, integral_smul_measure,
      haR, hbR, smul_eq_mul, smul_eq_mul]
  have hνu : ν.real Set.univ = 1 := by
    have : ν Set.univ = 1 := by
      simp only [hν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [ha, hb, ← ENNReal.ofReal_add hp0.le (by linarith)]
      simp
    simp [Measure.real, this]
  set m1 := ∫ s, x s ∂F1
  set m0 := ∫ s, x s ∂F0
  have key : p < m1 := by
    by_contra hcon
    push Not at hcon
    -- ∫ (x - p)^2 = p m1 - p^2 ≤ 0
    have hint : ∫ s, (x s - p) ^ 2 ∂ν = p * m1 - p ^ 2 := by
      have hexp : (fun s => (x s - p) ^ 2) = fun s => (x s * x s - 2 * p * x s) + p ^ 2 := by
        funext s; ring
      rw [hexp]
      have i1 : Integrable (fun s => x s * x s - 2 * p * x s) ν := hxxi.sub (hxi.const_mul _)
      have e1 : ∫ s, (x s * x s - 2 * p * x s) + p ^ 2 ∂ν
          = ∫ s, (x s * x s - 2 * p * x s) ∂ν + ∫ s, p ^ 2 ∂ν :=
        integral_add i1 (integrable_const _)
      have e2 : ∫ s, (x s * x s - 2 * p * x s) ∂ν
          = ∫ s, x s * x s ∂ν - ∫ s, 2 * p * x s ∂ν :=
        integral_sub hxxi (hxi.const_mul _)
      rw [e1, e2, integral_const_mul, E1, E2, integral_const, hνu]
      simp; ring
    have hnn : 0 ≤ᵐ[ν] fun s => (x s - p) ^ 2 := Eventually.of_forall fun s => sq_nonneg _
    have hsqi : Integrable (fun s => (x s - p) ^ 2) ν := by
      have hexp : (fun s => (x s - p) ^ 2) = fun s => (x s * x s - 2 * p * x s) + p ^ 2 := by
        funext s; ring
      rw [hexp]; exact (hxxi.sub (hxi.const_mul _)).add (integrable_const _)
    have hzero : ∫ s, (x s - p) ^ 2 ∂ν = 0 := by
      apply le_antisymm
      · rw [hint]; nlinarith
      · exact integral_nonneg fun s => sq_nonneg _
    rw [integral_eq_zero_iff_of_nonneg_ae hnn hsqi] at hzero
    -- x = p a.e.
    have hfa : (a • F1).rnDeriv ν =ᵐ[ν] fun _ => a := by
      filter_upwards [hzero, Measure.rnDeriv_lt_top (a • F1) ν] with s hs hlt
      have : x s = p := by
        have : (x s - p) ^ 2 = 0 := hs
        nlinarith [sq_nonneg (x s - p)]
      have e : a = ENNReal.ofReal ((a • F1).rnDeriv ν s).toReal := by rw [← hxdef, this]
      rw [ENNReal.ofReal_toReal hlt.ne] at e
      exact e.symm
    have hW : a • F1 = a • ν := by
      rw [← Measure.withDensity_rnDeriv_eq _ _ hac, withDensity_congr_ae hfa, withDensity_const]
    have hF1 : F1 = ν := by
      ext s hs
      have := congrArg (fun m : Measure S => m s) hW
      simp only [Measure.smul_apply, smul_eq_mul] at this
      exact (ENNReal.mul_right_inj ha0 hat).1 this
    apply hF
    ext s hs
    have h := congrArg (fun m : Measure S => m s) hF1
    simp only [hν, Measure.add_apply, Measure.smul_apply, smul_eq_mul] at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top hat (measure_ne_top _ _))
      (ENNReal.mul_ne_top hbt (measure_ne_top _ _)), ENNReal.toReal_mul,
      ENNReal.toReal_mul, haR, hbR] at h'
    have h'' : (F0 s).toReal = (F1 s).toReal := by
      have : (1 - p) * ((F1 s).toReal - (F0 s).toReal) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h''
  refine ⟨key, ?_⟩
  have : p * m1 + (1 - p) * m0 = p := by rw [← E3, E2]
  nlinarith
