-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RhoLtOneV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:50:08.246586+00:00
-- url     : https://prove2.me/submissions/df9ab67f-9f1d-476e-af82-b63a4a09ec5e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49SafeReservePositiveV1
import Theorems.Thm_Kyprianou_Ch04_exercise49PositiveInitialBlockV1
import Theorems.Thm_Kyprianou_Ch04_exercise49SurvivalFromBlocksV1
import Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvSmallTimeDrift
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Reduce the strict upper bound to favourable initial blocks and eventual safety. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift = triplet.drift -
      ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega)))
    (hTendsInfinity : ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop) :
    let tau : Real -> Omega -> WithTop NNReal := fun initial omega =>
          sInf {v : WithTop NNReal |
            ∃ t : NNReal, v = ↑t ∧ 0 < t ∧
              initial + X t omega < 0}
        let rho : Real := (P {omega : Omega | tau 0 omega ≠ ⊤}).toReal
        rho < 1 := by
  have hs := Kyprianou.Ch04.exercise49GeneralBvSmallTimeDrift
    P X hLevy triplet hTriplet hBV drift hDrift hd hNotSubordinator
  have hsafe := Kyprianou.Ch04.exercise49SafeReservePositiveV1 P X hLevy hTendsInfinity
  have hb := Kyprianou.Ch04.exercise49PositiveInitialBlockV1 P X hLevy drift hd hs
  simpa only [zero_add] using
    Kyprianou.Ch04.exercise49SurvivalFromBlocksV1 P X hLevy hsafe hb
