-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_exp_convolution_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:45:52.7803+00:00
-- url     : https://prove2.me/submissions/3d8163c2-edb1-4b43-9b64-752d32c30b49

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution
    (f : ℝ → ℝ) (φ L : ℝ) (hφ : 0 < φ)
    (hf : Measurable f) (h0 : ∀ t, 0 ≤ f t)
    (hb : ∀ t, f t ≤ L) (hl : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun z : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-φ*t) * f (z-t))
      atTop (𝓝 (L/φ)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hbound : Integrable (fun t : ℝ => L * Real.exp (-φ*t)) μ :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hφ) 0).const_mul L
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := (atTop : Filter ℝ))
    (F := fun z t : ℝ => Real.exp (-φ*t) * f (z-t))
    (f := fun t : ℝ => Real.exp (-φ*t) * L)
    (fun t => L * Real.exp (-φ*t))
    (Eventually.of_forall fun z =>
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
        (hf.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    (Eventually.of_forall fun z => ae_of_all μ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (h0 _))]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb (z-t)) (Real.exp_nonneg _))
    hbound
    (ae_of_all μ fun t => by
      have hz : Tendsto (fun z : ℝ => z-t) atTop atTop := by
        simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-t) tendsto_id
      exact (hl.comp hz).const_mul (Real.exp (-φ*t)))
  have hval : (∫ t, Real.exp (-φ*t) * L ∂μ) = L/φ := by
    rw [integral_mul_const]
    change (∫ t in Ioi (0 : ℝ), Real.exp (-φ*t)) * L = L/φ
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hφ)]
    simp [div_eq_mul_inv, mul_comm]
  rwa [hval] at ht
