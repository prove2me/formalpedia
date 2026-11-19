-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianLevyExponent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:38:24.222683+00:00
-- url     : https://prove2.me/submissions/806285e5-ae03-471f-b318-8e32f4562994
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianLevyMeasureSourceExact
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpCompensatorIntegrable
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpExponentValue
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    IsLevyMeasure Pi ∧
      ∀ theta : ℝ,
        IntegrableOn
          (fun x : ℝ => (1 - Complex.exp
              (Complex.I * ((theta * x : ℝ) : ℂ))))
          (Set.Ioi (0 : ℝ)) Pi ∧
        (∫ x in Set.Ioi (0 : ℝ),
          ((1 : ℂ) -
            Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂Pi) =
          Complex.sqrt (((b ^ 2 : ℝ) : ℂ) -
            2 * Complex.I * (theta : ℂ)) - (b : ℂ) := by
  exact ⟨Kyprianou.Ch01.inverseGaussianLevyMeasureSourceExact b hb,
    fun theta => ⟨Kyprianou.Ch01.inverseGaussianJumpCompensatorIntegrable
      b hb theta,
      Kyprianou.Ch01.inverseGaussianJumpExponentValue b hb theta⟩⟩
