-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_positiveDiscount_zeroBarrier
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:09:36.044129+00:00
-- url     : https://prove2.me/submissions/eb6f120c-3590-40e4-b0c0-eb2f28442700

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_zeroBarrier_BV
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_zeroBarrier_UBV

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Glue of the Proved BV/UBV leaves for the positive-discount zero-barrier transform.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
    forall (q : Real), 0 < q ->
          forall phi : Real,
      (0 <= phi ∧ L.ψ phi = q ∧ (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi)) ->
      (forall (x : Real), x = 0 ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x)) := by
  intro q hq phi hphi x hx finiteTime hfin
  by_cases hBV : L.BoundedVariation
  · exact firstPassageTransform_positiveDiscount_zeroBarrier_BV
      P F L hNotDecreasing hBV q hq phi hphi x hx finiteTime hfin
  · exact firstPassageTransform_positiveDiscount_zeroBarrier_UBV
      P F L hNotDecreasing hBV q hq phi hphi x hx finiteTime hfin
