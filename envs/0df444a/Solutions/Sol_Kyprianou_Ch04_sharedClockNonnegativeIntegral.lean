-- Prove2me | solution 1 for Kyprianou.Ch04.sharedClockNonnegativeIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:18:29.803401+00:00
-- url     : https://prove2.me/submissions/fb6275b5-dae3-42fb-b6a7-c2a7214c00b2

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Transfer a nonnegative integrable real kernel through an expected clock measure. -/
theorem solution
    {Omega E A : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Omega) (mu : Measure A) (R : Omega → Measure E)
    (q : Omega → E → A) (hq : ∀ w, Measurable (q w))
    (hR : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂(R w) ∂P) = ∫⁻ a, k a ∂mu)
    (f : A → ℝ) (hf : Measurable f) (h0 : ∀ a, 0 ≤ f a) (hi : Integrable f mu) :
    (∫ w, ∫ z, f (q w z) ∂(R w) ∂P) = ∫ a, f a ∂mu := by
  let L (w : Omega) := ∫⁻ z, ENNReal.ofReal (f (q w z)) ∂(R w)
  have hL := hR (fun a => ENNReal.ofReal (f a)) (ENNReal.measurable_ofReal.comp hf)
  have hfin : (∫⁻ w, L w ∂P) < ⊤ := by
    change (∫⁻ w, ∫⁻ z, ENNReal.ofReal (f (q w z)) ∂(R w) ∂P) < ⊤
    rw [hL.2]
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).1 hi.2
  have he : (fun w => ∫ z, f (q w z) ∂(R w)) = fun w => (L w).toReal := by
    funext w
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => h0 _)
      (hf.comp (hq w)).aestronglyMeasurable
  have hto : (fun w => ENNReal.ofReal (L w).toReal) =ᵐ[P] L := by
    filter_upwards [ae_lt_top' hL.1 hfin.ne] with w hw
    exact ENNReal.ofReal_toReal hw.ne
  rw [he, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hL.1.ennreal_toReal.aestronglyMeasurable,
    lintegral_congr_ae hto]
  change (∫⁻ w, ∫⁻ z, ENNReal.ofReal (f (q w z)) ∂(R w) ∂P).toReal = _
  rw [hL.2]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0)
    hf.aestronglyMeasurable).symm
