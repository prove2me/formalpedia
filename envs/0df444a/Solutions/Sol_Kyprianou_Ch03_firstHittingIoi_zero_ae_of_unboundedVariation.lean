-- Prove2me | solution 1 for Kyprianou.Ch03.firstHittingIoi_zero_ae_of_unboundedVariation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:35:40.720301+00:00
-- url     : https://prove2.me/submissions/2cd1c090-09d8-41be-88dc-4f4a8056d116

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_zero_of_positiveNearZero_core
import Theorems.Thm_AvramDividend_Classical_ae_positive_near_zero_of_unbounded_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hUnboundedVariation : ¬ L.BoundedVariation) :
    Filter.Eventually (fun omega : Omega =>
      firstHittingTime L.X (Set.Ioi (0 : Real)) omega = 0) (MeasureTheory.ae P) := by
  filter_upwards
    [AvramDividend.Classical.ae_positive_near_zero_of_unbounded_variation
      L hUnboundedVariation] with omega hNear
  exact Kyprianou.Ch03.firstHittingIoi_zero_of_positiveNearZero_core
    L.X omega (L.X_zero omega) hNear

