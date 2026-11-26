-- Prove2me | solution 1 for Kyprianou.Ch04.sharedClockPhysicalSubAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:22:36.100581+00:00
-- url     : https://prove2.me/submissions/dd34b1c4-7f86-4aa9-ac4a-af3dbe756989

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- The physical compensated integral is additive under subtraction on integrable kernels. -/
theorem solution
    {Omega E A : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Omega) (mu : Measure A) (R : Omega → Measure E) (S : Measure E)
    (q : Omega → E → A) (hq : ∀ w, Measurable (q w))
    (hR : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂(R w) ∂P) = ∫⁻ a, k a ∂mu)
    (hS : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂S) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂S ∂P) = ∫⁻ a, k a ∂mu)
    (f g : A → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f mu) (hgi : Integrable g mu) :
    let I := fun k : A → ℝ => fun w =>
      (∫ z, k (q w z) ∂(R w)) - ∫ z, k (q w z) ∂S
    I (f - g) =ᵐ[P] I f - I g := by
  have aux (K : Omega → Measure E)
      (hK : ∀ k : A → ENNReal, Measurable k →
        AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(K w)) P ∧
        (∫⁻ w, ∫⁻ z, k (q w z) ∂(K w) ∂P) = ∫⁻ a, k a ∂mu)
      (k : A → ℝ) (hk : Measurable k) (hi : Integrable k mu) :
      ∀ᵐ w ∂P, Integrable (fun z => k (q w z)) (K w) := by
    have h := hK (fun a => ENNReal.ofReal ‖k a‖)
      (ENNReal.measurable_ofReal.comp hk.norm)
    have hfin : (∫⁻ w, ∫⁻ z, ENNReal.ofReal ‖k (q w z)‖ ∂(K w) ∂P) < ⊤ := by
      rw [h.2]
      exact (hasFiniteIntegral_iff_norm k).1 hi.2
    filter_upwards [ae_lt_top' h.1 hfin.ne] with w hw
    exact ⟨(hk.comp (hq w)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_norm (fun z => k (q w z))).2 hw⟩
  dsimp only
  filter_upwards [aux R hR f hf hfi, aux R hR g hg hgi,
    aux (fun _ => S) hS f hf hfi, aux (fun _ => S) hS g hg hgi] with w hrf hrg hsf hsg
  simp only [Pi.sub_apply, integral_sub hrf hrg, integral_sub hsf hsg]
  ring
