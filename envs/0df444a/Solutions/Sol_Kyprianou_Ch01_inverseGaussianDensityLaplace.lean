-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianDensityLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:07:37.330802+00:00
-- url     : https://prove2.me/submissions/e2c36a2a-8c29-49dc-88e3-fea183d166a7

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityMassOne
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityDiscountIntegrable
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplaceIntegralValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped NNReal ENNReal Interval
set_option autoImplicit false

theorem solution
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    IG Set.univ = 1 ∧
    ∀ q : ℝ, 0 ≤ q →
      Integrable (fun x : ℝ => Real.exp (-q * x)) IG ∧
      (∫ x, Real.exp (-q * x) ∂IG) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by
  dsimp
  refine ⟨?_, ?_⟩
  · exact Kyprianou.Ch01.inverseGaussianDensityMassOne s b hs hb
  · intro q hq
    exact ⟨Kyprianou.Ch01.inverseGaussianDensityDiscountIntegrable
        s b hs hb q hq,
      Kyprianou.Ch01.inverseGaussianDensityLaplaceIntegralValue
        s b hs hb q hq⟩
