-- Prove2me | solution 1 for Kyprianou.Ch04.sharedClockPhysicalL1Difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:54:18.019444+00:00
-- url     : https://prove2.me/submissions/67b78697-2307-4519-b190-26defbda3450

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_aeFiniteExpectedAbsoluteRandomIntegral
import Theorems.Thm_Kyprianou_Ch04_physicalCompensatedL1DifferenceBound
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Shared expected-clock measure controls physical compensated L1 differences. -/
theorem solution
    {Omega E A : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Omega) (mu : Measure A)
    (R : Omega → Measure E) (S : Measure E) (q : Omega → E → A)
    (hq : ∀ w, Measurable (q w))
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
    Integrable (I f) P ∧ Integrable (I g) P ∧
      (∫ w, |I f w - I g w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu := by
  have aux (K : Omega → Measure E)
      (hK : ∀ k : A → ENNReal, Measurable k →
        AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(K w)) P ∧
        (∫⁻ w, ∫⁻ z, k (q w z) ∂(K w) ∂P) = ∫⁻ a, k a ∂mu)
      (k : A → ℝ) (hk : Measurable k) (hki : Integrable k mu) :
      (∀ᵐ w ∂P, Integrable (fun z => k (q w z)) (K w)) ∧
      Integrable (fun w => ∫ z, |k (q w z)| ∂(K w)) P ∧
      (∫ w, ∫ z, |k (q w z)| ∂(K w) ∂P) = ∫ a, |k a| ∂mu ∧
      Integrable (fun w => ∫ z, k (q w z) ∂(K w)) P := by
    have hm : Measurable (fun a => ENNReal.ofReal |k a|) :=
      ENNReal.measurable_ofReal.comp hk.abs
    have hL := hK _ hm
    have hfin : (∫⁻ w, ∫⁻ z, ENNReal.ofReal |k (q w z)| ∂(K w) ∂P) < ⊤ := by
      rw [hL.2]
      simpa only [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm k).1 hki.2
    have h := Kyprianou.Ch04.aeFiniteExpectedAbsoluteRandomIntegral P K
      (fun w z => k (q w z))
      (Eventually.of_forall fun w => (hk.comp (hq w)).aestronglyMeasurable)
      hL.1 (hK _ (ENNReal.measurable_ofReal.comp hk)).1
      (hK _ (ENNReal.measurable_ofReal.comp hk.neg)).1 hfin
    refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
    rw [h.2.2.1, hL.2]
    symm
    exact integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun a => abs_nonneg (k a)) hk.abs.aestronglyMeasurable
  have rf := aux R hR f hf hfi
  have rg := aux R hR g hg hgi
  have sf := aux (fun _ => S) hS f hf hfi
  have sg := aux (fun _ => S) hS g hg hgi
  have rd := aux R hR (fun a => f a - g a) (hf.sub hg) (hfi.sub hgi)
  have sd := aux (fun _ => S) hS (fun a => f a - g a) (hf.sub hg) (hfi.sub hgi)
  let If := fun w => (∫ z, f (q w z) ∂(R w)) - ∫ z, f (q w z) ∂S
  let Ig := fun w => (∫ z, g (q w z) ∂(R w)) - ∫ z, g (q w z) ∂S
  have hIf : Integrable If P := rf.2.2.2.sub sf.2.2.2
  have hIg : Integrable Ig P := rg.2.2.2.sub sg.2.2.2
  refine ⟨hIf, hIg, ?_⟩
  have hb := Kyprianou.Ch04.physicalCompensatedL1DifferenceBound P R S
    (fun w z => f (q w z)) (fun w z => g (q w z))
    rf.1 rg.1 sf.1 sg.1
    (fun w => ∫ z, |f (q w z) - g (q w z)| ∂(R w))
    (fun w => ∫ z, |f (q w z) - g (q w z)| ∂S)
    (fun w => If w - Ig w)
    (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun _ => rfl)
    (Eventually.of_forall fun _ => rfl) (hIf.sub hIg).aestronglyMeasurable
    rd.2.1 sd.2.1 (rd.2.2.1.trans sd.2.2.1.symm)
  rw [← sd.2.2.1]
  exact hb.2
