-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46CountableSectionsProductNullV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:49.036099+00:00
-- url     : https://prove2.me/submissions/aba124bb-73f4-47c9-9cb6-1ed9a49d83c1

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (m : Measure NNReal) [SFinite m] [NullSingletonClass m]
    (S : Set (Omega × NNReal)) (hS : MeasurableSet S)
    (hCount : ∀ᵐ w ∂P, (Prod.mk w ⁻¹' S).Countable) :
    (P.prod m) S = 0 := by
  rw [Measure.prod_apply hS]
  calc
    (∫⁻ w, m (Prod.mk w ⁻¹' S) ∂P) = ∫⁻ _ : Omega, 0 ∂P :=
      lintegral_congr_ae (hCount.mono fun w hw => hw.measure_zero m)
    _ = 0 := lintegral_zero
