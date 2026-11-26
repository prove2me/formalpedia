-- Prove2me | solution 1 for Kyprianou.Ch04.sharedClockSignedIntegrabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:13:15.186739+00:00
-- url     : https://prove2.me/submissions/dc532012-6114-435b-841c-e3e965451dc2

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_aeFiniteExpectedAbsoluteRandomIntegral
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Integrability of pathwise and outer signed clock integrals. -/
theorem solution {Ω E A : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Ω) (μ : Measure A) (R : Ω → Measure E)
    (q : Ω → E → A) (hq : ∀ w, Measurable (q w))
    (hR : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂(R w) ∂P) = ∫⁻ a, k a ∂μ)
    (f : A → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    (∀ᵐ w ∂P, Integrable (fun z => f (q w z)) (R w)) ∧
      Integrable (fun w => ∫ z, f (q w z) ∂(R w)) P := by
  have hm := hR (fun a => ENNReal.ofReal |f a|) (ENNReal.measurable_ofReal.comp hf.abs)
  have hfin : (∫⁻ w, ∫⁻ z, ENNReal.ofReal |f (q w z)| ∂(R w) ∂P) < ⊤ := by
    rw [hm.2]
    simpa only [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm f).1 hi.2
  have h := Kyprianou.Ch04.aeFiniteExpectedAbsoluteRandomIntegral P R
    (fun w z => f (q w z))
    (Eventually.of_forall fun w => (hf.comp (hq w)).aestronglyMeasurable)
    hm.1 (hR _ (ENNReal.measurable_ofReal.comp hf)).1
    (hR _ (ENNReal.measurable_ofReal.comp hf.neg)).1 hfin
  exact ⟨h.1,h.2.2.2⟩
