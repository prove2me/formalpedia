-- Prove2me | solution 1 for Kyprianou.Ch03.nonnegativeDensityExtendCutV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:54:29.1028+00:00
-- url     : https://prove2.me/submissions/39757285-273c-4f1b-84be-af707dbf513b

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : ℕ → Set Omega) (Z : Omega → ℝ)
    (hB : ∀ n, MeasurableSet (B n)) (hmono : Monotone B)
    (hZ : ∀ omega, 0 ≤ Z omega)
    (hint : ∀ n, Integrable ((B n).indicator Z) P)
    (heq : ∀ n, Q (B n) = ENNReal.ofReal (∫ omega, (B n).indicator Z omega ∂P)) :
    Q (⋃ n, B n) = ENNReal.ofReal (∫ omega, (⋃ n, B n).indicator Z omega ∂P) := by
  let R := P.withDensity (fun w => ENNReal.ofReal (Z w))
  have hi : ∀ n, IntegrableOn Z (B n) P :=
    fun n => (integrable_indicator_iff (hB n)).mp (hint n)
  have he : ∀ n, Q (B n) = R (B n) := by
    intro n
    rw [heq n, integral_indicator (hB n), withDensity_apply _ (hB n)]
    exact ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall hZ)
  have hu : Q (⋃ n, B n) = R (⋃ n, B n) := by
    rw [hmono.measure_iUnion, hmono.measure_iUnion]
    simp_rw [he]
  have hm := MeasurableSet.iUnion hB
  have hz : AEMeasurable Z (P.restrict (⋃ n, B n)) :=
    aemeasurable_iUnion_iff.mpr (fun n => (hi n).aestronglyMeasurable.aemeasurable)
  rw [integral_indicator hm, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hZ) hz.aestronglyMeasurable, ← withDensity_apply _ hm,
    ← hu, ENNReal.ofReal_toReal (measure_ne_top Q _)]
