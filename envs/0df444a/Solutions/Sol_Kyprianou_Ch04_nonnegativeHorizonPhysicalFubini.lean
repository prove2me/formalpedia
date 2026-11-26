-- Prove2me | solution 1 for Kyprianou.Ch04.nonnegativeHorizonPhysicalFubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:05.0077+00:00
-- url     : https://prove2.me/submissions/e3197323-b09a-4f63-88b7-3c43a87b708e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityHorizonProd
import Theorems.Thm_Kyprianou_Ch04_nestedNonnegativeIntegralToReal
import Theorems.Thm_Kyprianou_Ch04_jointNestedNonnegIntegralsMeasurable
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Identify the physical intensity integral with the nested time-mark integral. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (nu : Measure ℝ) [SigmaFinite nu] (t : NNReal)
    (f : Omega → ℝ × ℝ → ℝ)
    (hf : Measurable (fun z : Omega × (ℝ × ℝ) => f z.1 z.2))
    (hn : ∀ w z, 0 ≤ f w z)
    (hFin : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (f w (s,x)) ∂nu ∂volume ∂P) < ⊤) :
    (∀ w, (∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      ENNReal.ofReal (f w z) ∂referenceIntensity nu) =
      ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ), ∫⁻ x,
        ENNReal.ofReal (f w (s,x)) ∂nu ∂volume) ∧
    (∀ᵐ w ∂P, (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      f w z ∂referenceIntensity nu) =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, f w (s,x) ∂nu ∂volume) := by
  let V := volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))
  have hsection (w : Omega) : Measurable (f w) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hENN (w : Omega) :
      (∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        ENNReal.ofReal (f w z) ∂referenceIntensity nu) =
      ∫⁻ s, ∫⁻ x, ENNReal.ofReal (f w (s,x)) ∂nu ∂V := by
    rw [referenceIntensityHorizonProd nu t]
    exact lintegral_prod _ (ENNReal.measurable_ofReal.comp (hsection w)).aemeasurable
  refine ⟨hENN,?_⟩
  have hm := (jointNestedNonnegIntegralsMeasurable V nu
    (fun z : Omega × (ℝ × ℝ) => f z.1 z.2) hf).1
  filter_upwards [ae_lt_top' hm.aemeasurable hFin.ne] with w hw
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (hn w))
    (hsection w).aestronglyMeasurable, hENN w]
  exact (nestedNonnegativeIntegralToReal V nu (f w) (hsection w) (hn w) hw.ne).symm
