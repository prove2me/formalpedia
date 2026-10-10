-- Prove2me | solution 1 for MeasureTheory.eqOn_of_le_setAverage
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T15:54:36.008077+00:00
-- url     : https://prove2.me/submissions/b38099cc-1457-41bc-b7ec-fd133fe66516

import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false

theorem solution {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsOpenPosMeasure μ]
    {s : Set X} {f : X → ℝ} (hs : IsOpen s) (hfinite : μ s ≠ ∞)
    (hc : ContinuousOn f s) (hi : IntegrableOn f s μ)
    (hle : ∀ x ∈ s, f x ≤ ⨍ y in s, f y ∂μ) :
    EqOn f (fun _ => ⨍ y in s, f y ∂μ) s := by
  letI : Fact (μ s < ∞) := ⟨hfinite.lt_top⟩
  have hnonneg : 0 ≤ᵐ[μ.restrict s] (fun x => (⨍ y in s, f y ∂μ) - f x) :=
    (ae_restrict_mem hs.measurableSet).mono fun x hx => sub_nonneg.mpr (hle x hx)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    ((integrable_const _).sub hi)).mp (setIntegral_setAverage_sub hfinite hi)
  have heq : f =ᵐ[μ.restrict s] (fun _ => ⨍ y in s, f y ∂μ) :=
    hz.mono fun x hx => (sub_eq_zero.mp hx).symm
  exact eqOn_open_of_ae_eq heq hs hc continuousOn_const
