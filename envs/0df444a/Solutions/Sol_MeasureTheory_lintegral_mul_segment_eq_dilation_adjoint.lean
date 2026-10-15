-- Prove2me | solution 1 for MeasureTheory.lintegral_mul_segment_eq_dilation_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T08:07:48.516449+00:00
-- url     : https://prove2.me/submissions/e71b09c3-8f6b-4ab8-a079-29276bb2e206

import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Set Metric
open scoped ENNReal
set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    [SFinite μ] (f h : E → ENNReal) (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ z, h z * (∫⁻ t in Icc (0 : ℝ) 1, f (t • z)) ∂μ) =
      ∫⁻ y, f y * (∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal ((t ^ Module.finrank ℝ E)⁻¹) * h (t⁻¹ • y)) ∂μ := by
  have hi : volume.restrict (Icc (0 : ℝ) 1) = volume.restrict (Ioc (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  simp only [hi]
  have hc (z : E) : h z * (∫⁻ t in Ioc (0 : ℝ) 1, f (t • z)) =
      ∫⁻ t in Ioc (0 : ℝ) 1, h z * f (t • z) :=
    (lintegral_const_mul _ (hf.comp (measurable_id.smul measurable_const))).symm
  simp only [hc]
  rw [lintegral_lintegral_swap]
  · calc
      (∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z, h z * f (t • z) ∂μ) =
          ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y,
            f y * (ENNReal.ofReal ((t ^ Module.finrank ℝ E)⁻¹) * h (t⁻¹ • y)) ∂μ := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 t ht.1.ne')).toMeasurableEquiv
        have he : (∫⁻ y, h (t⁻¹ • y) * f y ∂Measure.map e μ) =
            ∫⁻ z, h z * f (t • z) ∂μ := by
          rw [lintegral_map_equiv]
          congr 1
          ext z
          simp [e, smul_smul, inv_mul_cancel₀ ht.1.ne']
        dsimp only
        rw [← he]
        change (∫⁻ y, h (t⁻¹ • y) * f y ∂Measure.map (t • ·) μ) = _
        rw [Measure.map_addHaar_smul μ ht.1.ne', lintegral_smul_measure,
          abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht.1.le _)), smul_eq_mul]
        rw [← lintegral_const_mul]
        · apply lintegral_congr
          intro y
          ac_rfl
        · exact ((hh.comp (measurable_const.smul measurable_id)).mul hf)
      _ = _ := by
        rw [lintegral_lintegral_swap]
        · congr 1
          ext y
          rw [lintegral_const_mul]
          exact ((measurable_id.pow_const _).inv.ennreal_ofReal.mul
            (hh.comp (measurable_id.inv.smul measurable_const)))
        · exact ((hf.comp measurable_snd).mul
            (((measurable_fst.pow_const _).inv.ennreal_ofReal).mul
              (hh.comp (measurable_fst.inv.smul measurable_snd)))).aemeasurable
  · exact ((hh.comp measurable_fst).mul
      (hf.comp (measurable_snd.smul measurable_fst))).aemeasurable
