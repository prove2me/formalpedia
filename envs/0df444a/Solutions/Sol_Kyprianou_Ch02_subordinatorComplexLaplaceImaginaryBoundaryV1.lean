-- Prove2me | solution 1 for Kyprianou.Ch02.subordinatorComplexLaplaceImaginaryBoundaryV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:47:27.157661+00:00
-- url     : https://prove2.me/submissions/cd75c6b0-2ce0-4e4c-a59d-1a481203b48d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) (d : ℝ) (t : ℝ≥0)
    (hchar : ∀ ξ : ℝ, charFun Q ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        (Complex.I * ((d * ξ : ℝ) : ℂ) +
          ∫ x in Set.Ioi (0 : ℝ),
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν))) :
    let Ξ : ℂ → ℂ := fun z => (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν
    ∀ y : ℝ, (∫ x, Complex.exp (-((y : ℂ) * Complex.I) * (x : ℂ)) ∂Q) =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ ((y : ℂ) * Complex.I)) := by
  dsimp
  intro y
  have hl : (∫ x, Complex.exp (-((y : ℂ) * Complex.I) * (x : ℂ)) ∂Q) =
      charFun Q (-y) := by
    rw [charFun_apply_real]
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    push_cast
    ring
  rw [hl, hchar]
  congr 1
  rw [show (∫ x in Set.Ioi (0 : ℝ),
      (1 - Complex.exp (-((y : ℂ) * Complex.I) * (x : ℂ))) ∂ν) =
      -(∫ x in Set.Ioi (0 : ℝ),
        (Complex.exp (Complex.I * ((((-y) * x : ℝ) : ℂ))) - 1) ∂ν) by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [show -((y : ℂ) * Complex.I) * (x : ℂ) =
      Complex.I * ((((-y) * x : ℝ) : ℂ)) by push_cast; ring]
    ring]
  push_cast
  ring
