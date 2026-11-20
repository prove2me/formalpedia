-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianDensityDiscountIntegrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:54:27.025351+00:00
-- url     : https://prove2.me/submissions/7a1023a9-9282-4bc8-9728-b5c2415249f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityMassOne
import Theorems.Thm_Kyprianou_Ch01_finitePositiveSupportDiscountIntegrable
open MeasureTheory Set Complex Kyprianou.Ch01
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    ∀ q : ℝ, 0 ≤ q → Integrable (fun x : ℝ => Real.exp (-q * x)) IG := by
  intro IG q hq
  have hmass : IG Set.univ = 1 := by
    simpa only [IG] using
      (Kyprianou.Ch01.inverseGaussianDensityMassOne s b hs hb)
  have hfinite : IG Set.univ < ∞ := by
    rw [hmass]
    exact ENNReal.one_lt_top
  have hAC : IG ≪ volume.restrict (Set.Ioi (0 : ℝ)) := by
    dsimp [IG]
    exact withDensity_absolutelyContinuous _ _
  have hpositive : ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact le_of_lt hx
  have hsupp : ∀ᵐ x ∂IG, 0 ≤ x := hAC.ae_le hpositive
  exact Kyprianou.Ch01.finitePositiveSupportDiscountIntegrable
    IG hfinite hsupp q hq
