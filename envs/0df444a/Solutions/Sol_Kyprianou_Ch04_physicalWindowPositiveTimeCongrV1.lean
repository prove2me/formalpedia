-- Prove2me | solution 1 for Kyprianou.Ch04.physicalWindowPositiveTimeCongrV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:29:48.590915+00:00
-- url     : https://prove2.me/submissions/c0b3d84b-453c-4b97-9288-e855fcb75675

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

/-- Integrands agreeing at positive times have identical closed-window integrals
when the measure has no mass on the initial time slice. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : ℝ) (B : Set ℝ)
    (hB : MeasurableSet B)
    (hz : R (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (k l : ℝ × ℝ → ℝ)
    (he : ∀ z, 0 < z.1 → z.1 ≤ T → z.2 ∈ B → k z = l z) :
    (∫ z in Icc 0 T ×ˢ B, k z ∂ R) = ∫ z in Icc 0 T ×ˢ B, l z ∂ R := by
  have hae : ∀ᵐ z ∂ R, z.1 ≠ 0 := by
    apply ae_iff.mpr
    have hs : {z : ℝ × ℝ | ¬ z.1 ≠ 0} ⊆ ({0} : Set ℝ) ×ˢ (univ : Set ℝ) :=
      fun z hz => ⟨by simpa using hz,mem_univ _⟩
    exact measure_mono_null hs hz
  apply setIntegral_congr_ae (measurableSet_Icc.prod hB)
  filter_upwards [hae] with z hz hzD
  exact he z (lt_of_le_of_ne hzD.1.1 (Ne.symm hz)) hzD.1.2 hzD.2
