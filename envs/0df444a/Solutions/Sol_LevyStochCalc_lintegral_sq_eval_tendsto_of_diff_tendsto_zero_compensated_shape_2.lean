-- Prove2me | solution 2 for LevyStochCalc.lintegral_sq_eval_tendsto_of_diff_tendsto_zero_compensated_shape
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:39:49.835291+00:00
-- url     : https://prove2.me/submissions/5cc7efb6-8048-4a2a-be43-a3db8e93bb41

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

theorem AuxLsb.formula {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {μ : Measure α} {η : Measure γ} [SFinite μ] [SFinite η] {T : ℝ}
    (g : α × ℝ × γ → ℝ) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z, (‖g (x, y, z)‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ
      = eLpNorm g 2 (μ.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod η)) ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ← ENNReal.rpow_mul]
  have hm : Measurable (fun w : α × ℝ × γ => (‖g w‖₊ : ℝ≥0∞) ^ 2) :=
    (hg.nnnorm.coe_nnreal_ennreal).pow_const 2
  simp only [ENNReal.toReal_ofNat]
  norm_num
  simp only [enorm_eq_nnnorm]
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hx : Measurable (fun w : ℝ × γ => (‖g (x, w)‖₊ : ℝ≥0∞) ^ 2) :=
    hm.comp measurable_prodMk_left
  rw [lintegral_prod _ hx.aemeasurable]

theorem AuxLsb.tend
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f : α → E} {fn : ℕ → α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hfn : ∀ n, MeasureTheory.AEStronglyMeasurable (fn n) μ)
    (h_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n - f) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n) p μ) Filter.atTop
      (nhds (MeasureTheory.eLpNorm f p μ)) := by
  have up : ∀ n, eLpNorm (fn n) p μ ≤ eLpNorm (fn n - f) p μ + eLpNorm f p μ := by
    intro n
    have := eLpNorm_add_le ((hfn n).sub hf) hf hp
    simpa using this
  have lo : ∀ n, eLpNorm f p μ ≤ eLpNorm (fn n - f) p μ + eLpNorm (fn n) p μ := by
    intro n
    have := eLpNorm_add_le (hf.sub (hfn n)) (hfn n) hp
    have e : f - fn n = -(fn n - f) := (neg_sub _ _).symm
    rw [e, eLpNorm_neg] at this
    simpa using this
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 ha
    have hev : ∀ᶠ n in Filter.atTop, eLpNorm (fn n - f) p μ < r :=
      (tendsto_order.1 h_tendsto).2 _ (by exact_mod_cast hr0)
    filter_upwards [hev] with n hn
    have h1 : a + r < r + eLpNorm (fn n) p μ :=
      lt_of_lt_of_le hr ((lo n).trans (add_le_add hn.le le_rfl))
    rw [add_comm] at h1
    exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 h1
  · have ht : Filter.Tendsto (fun n => eLpNorm (fn n - f) p μ + eLpNorm f p μ) Filter.atTop
        (nhds (0 + eLpNorm f p μ)) := h_tendsto.add tendsto_const_nhds
    rw [zero_add] at ht
    filter_upwards [(tendsto_order.1 ht).2 _ hb] with n hn
    exact lt_of_le_of_lt (up n) hn

theorem _root_.solution
    {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {μ : Measure α} {η : Measure γ} [SFinite μ] [SFinite η]
    {T : ℝ}
    (H : α → ℝ → γ → ℝ)
    (h_H_meas : Measurable (fun (p : α × ℝ × γ) => H p.1 p.2.1 p.2.2))
    (ev : ℕ → ℝ → γ → α → ℝ)
    (h_ev_meas : ∀ n, Measurable (fun (p : α × ℝ × γ) => ev n p.2.1 p.2.2 p.1))
    (h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
        (‖H x y z - ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
        (‖ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ)
      Filter.atTop
      (nhds (∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
        (‖H x y z‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ)) := by
  set ν := μ.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod η)
  let h : α × ℝ × γ → ℝ := fun p => H p.1 p.2.1 p.2.2
  let fn : ℕ → α × ℝ × γ → ℝ := fun n p => ev n p.2.1 p.2.2 p.1
  have eH : ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z, (‖H x y z‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ
      = eLpNorm h 2 ν ^ (2 : ℝ) := AuxLsb.formula (μ := μ) (η := η) (T := T) h h_H_meas
  have eF : ∀ n, ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z, (‖ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ
      = eLpNorm (fn n) 2 ν ^ (2 : ℝ) := fun n => AuxLsb.formula (fn n) (h_ev_meas n)
  have eD : ∀ n, ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
        (‖H x y z - ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ
      = eLpNorm (fn n - h) 2 ν ^ (2 : ℝ) := by
    intro n
    have := AuxLsb.formula (μ := μ) (η := η) (T := T) (h - fn n) (h_H_meas.sub (h_ev_meas n))
    rw [show fn n - h = -(h - fn n) from (neg_sub _ _).symm, eLpNorm_neg, ← this]
    rfl
  simp_rw [eD] at h_L2_diff
  have hd : Filter.Tendsto (fun n => eLpNorm (fn n - h) 2 ν) Filter.atTop (nhds 0) := by
    have := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0 |>.comp h_L2_diff
    simp only [Function.comp_def] at this
    have e0 : (0 : ℝ≥0∞) ^ (2 : ℝ)⁻¹ = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    rw [e0] at this
    refine this.congr fun n => ?_
    exact ENNReal.rpow_rpow_inv (by norm_num) _
  have ht := AuxLsb.tend (le_refl _ |>.trans' (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    h_H_meas.aestronglyMeasurable (fun n => (h_ev_meas n).aestronglyMeasurable) hd
  simp_rw [eF]
  rw [eH]
  exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _ |>.comp ht

end LevyStochCalc
