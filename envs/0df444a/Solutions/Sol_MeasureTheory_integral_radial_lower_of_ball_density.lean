-- Prove2me | solution 1 for MeasureTheory.integral_radial_lower_of_ball_density
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T21:45:52.688982+00:00
-- url     : https://prove2.me/submissions/516f2eb3-0ab1-4b8f-8fed-dafe01ef14e5

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

open MeasureTheory Set
open scoped ENNReal

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (t δ c : ℝ)
    (hδ : 0 < δ) (hc : 0 ≤ c) (f : ℝ → ℝ)
    (hf : Continuous f) (hnonneg : ∀ r ∈ Ici (0 : ℝ), 0 ≤ f r)
    (hmono : AntitoneOn f (Ici (0 : ℝ)))
    (hdensity : ∀ r : ℝ, 0 < r → r < δ →
      ENNReal.ofReal c ≤ μ (Metric.ball t r) / volume (Metric.ball t r)) :
    2 * c * (∫ r : ℝ in 0..δ, f r) ≤ ∫ x : ℝ, f |x - t| ∂μ := by
  let F : ℝ → ℝ := fun x => f |x-t|
  have hFc : Continuous F := hf.comp (by fun_prop)
  have hFn : ∀ x, 0 ≤ F x := fun x => hnonneg _ (mem_Ici.2 (abs_nonneg _))
  have hFi : Integrable F μ := by
    apply Integrable.of_bound hFc.aestronglyMeasurable (f 0)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFn x)]
      exact hmono (by simp) (mem_Ici.2 (abs_nonneg _)) (abs_nonneg _)
  rcases hc.eq_or_lt with heq | hcpos
  · rw [← heq]
    simpa using integral_nonneg hFn
  let ν : Measure ℝ := volume.restrict (Ioo 0 δ)
  have hfn : 0 ≤ᵐ[ν] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hnonneg r (mem_Ici.2 hr.1.le)
  have hfi : Integrable f ν := by
    exact (hf.intervalIntegrable (μ := volume) 0 δ).1.mono_set Ioo_subset_Ioc_self
  have hsuper : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal (2*c) * ν {r | y < f r} ≤ μ {x | y < F x} := by
    intro y hy
    let M := (μ {x | y < F x}).toReal
    have hM : 0 ≤ M := ENNReal.toReal_nonneg
    have hbound : ∀ r ∈ Ioo (0 : ℝ) δ, y < f r → 2*c*r ≤ M := by
      intro r hr hyr
      have hr0 : 0 < r := hr.1
      have hb : ENNReal.ofReal c * volume (Metric.ball t r) ≤ μ (Metric.ball t r) :=
        (ENNReal.le_div_iff_mul_le (Or.inl (by
          rw [Real.volume_ball]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'))
          (Or.inl (by rw [Real.volume_ball]; exact ENNReal.ofReal_ne_top))).1
          (hdensity r hr.1 hr.2)
      have hs : Metric.ball t r ⊆ {x | y < F x} := by
        intro x hx
        rw [Metric.mem_ball, Real.dist_eq] at hx
        exact hyr.trans_le (hmono (mem_Ici.2 (abs_nonneg _)) (mem_Ici.2 hr.1.le) hx.le)
      have hh := hb.trans (measure_mono hs)
      rw [Real.volume_ball, ← ENNReal.ofReal_mul hc] at hh
      have hh' := ENNReal.toReal_mono (measure_ne_top μ _) hh
      rw [ENNReal.toReal_ofReal (mul_nonneg hc (by positivity))] at hh'
      simpa only [M, mul_assoc, mul_comm, mul_left_comm] using hh'
    have hs : {r | y < f r} ∩ Ioo (0 : ℝ) δ ⊆ Ioc 0 (M / (2*c)) := by
      intro r hr
      exact ⟨hr.2.1, (le_div_iff₀ (by positivity)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hbound r hr.2 hr.1)⟩
    have hv : ν {r | y < f r} ≤ ENNReal.ofReal (M / (2*c)) := by
      have hmeas : MeasurableSet {r | y < f r} :=
        (hf.isOpen_preimage _ isOpen_Ioi).measurableSet
      dsimp only [ν]
      rw [Measure.restrict_apply hmeas]
      exact (measure_mono hs).trans_eq (by rw [Real.volume_Ioc, sub_zero])
    calc
      ENNReal.ofReal (2*c) * ν {r | y < f r} ≤
          ENNReal.ofReal (2*c) * ENNReal.ofReal (M / (2*c)) := mul_le_mul' le_rfl hv
      _ = ENNReal.ofReal M := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_div_cancel₀ _ (by positivity)]
      _ = μ {x | y < F x} := ENNReal.ofReal_toReal (measure_ne_top μ _)
  have hlin : ENNReal.ofReal (2*c) * (∫⁻ r, ENNReal.ofReal (f r) ∂ν) ≤
      ∫⁻ x, ENNReal.ofReal (F x) ∂μ := by
    rw [lintegral_eq_lintegral_meas_lt ν hfn hf.measurable.aemeasurable,
      lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hFn) hFc.measurable.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hsuper y hy
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hfn,
    ← ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hFn),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*c)] at hlin
  have hreal := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hFn)).1 hlin
  have heq : (∫ r, f r ∂ν) = ∫ r in 0..δ, f r := by
    rw [intervalIntegral.integral_of_le hδ.le, integral_Ioc_eq_integral_Ioo]
  rwa [heq] at hreal
