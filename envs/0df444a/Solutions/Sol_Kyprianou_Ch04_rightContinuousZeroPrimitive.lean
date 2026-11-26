-- Prove2me | solution 1 for Kyprianou.Ch04.rightContinuousZeroPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:20:45.562366+00:00
-- url     : https://prove2.me/submissions/b9692d82-899a-4812-8693-6ef45698192e

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A right-continuous time density whose primitive vanishes identically must vanish. -/
theorem solution (g : ℝ → ℝ) (hm : Measurable g)
    (hi : ∀ t : NNReal, IntegrableOn g (Icc (0 : ℝ) (t : ℝ)) volume)
    (hr : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt g (Ici s) s)
    (hz : ∀ t : NNReal, (∫ r in Icc (0 : ℝ) (t : ℝ), g r ∂volume) = 0) :
    ∀ s : ℝ, 0 ≤ s → g s = 0 := by
  intro s hs
  have hsi : IntervalIntegrable g volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs]
    exact (hi s.toNNReal).mono_set (by rw [Real.coe_toNNReal _ hs]; exact Ioc_subset_Icc_self)
  have hd : HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, g r) (g s) (Ici s) s := by
    apply intervalIntegral.integral_hasDerivWithinAt_right (t := Ioi s) hsi
    · exact hm.stronglyMeasurable.stronglyMeasurableAtFilter
    · exact (hr s hs).mono Ioi_subset_Ici_self
  have he : EqOn (fun u => ∫ r in (0 : ℝ)..u, g r) (fun _ => (0 : ℝ)) (Ici s) := by
    intro u hu
    have hu0 : 0 ≤ u := hs.trans hu
    change (∫ r in (0 : ℝ)..u, g r) = 0
    rw [intervalIntegral.integral_of_le hu0,← integral_Icc_eq_integral_Ioc]
    simpa only [Real.coe_toNNReal _ hu0] using hz u.toNNReal
  have hc : HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, g r) 0 (Ici s) s :=
    (hasDerivWithinAt_const s (Ici s) (0 : ℝ)).congr he (he (le_refl s))
  exact (hd.derivWithin (uniqueDiffWithinAt_Ici s)).symm.trans
    (hc.derivWithin (uniqueDiffWithinAt_Ici s))
