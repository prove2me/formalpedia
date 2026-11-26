-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FiniteArrivalIntensityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:57:28.938135+00:00
-- url     : https://prove2.me/submissions/2c5995b7-f310-40e4-8ea5-b695ad87021d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν = ENNReal.ofReal lambda • service.map (fun x : Real => -x)) :
    L.ν (Iio (0 : Real)) = ENNReal.ofReal lambda := by
  rw [hInputLaw, Measure.smul_apply, Measure.map_apply measurable_neg measurableSet_Iio]
  have hpre : (fun x : Real => -x) ⁻¹' Iio (0 : Real) = Ioi (0 : Real) := by
    ext x
    simp
  rw [hpre, hServicePositive]
  simp
