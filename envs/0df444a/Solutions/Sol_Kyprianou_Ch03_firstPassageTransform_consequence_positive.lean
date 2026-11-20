-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_consequence_positive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:09:44.473355+00:00
-- url     : https://prove2.me/submissions/85c6f483-ab73-4a2a-bc9d-b360a378b466
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_zeroBarrier
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_strictBarrier
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

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
      (forall (x : Real), 0 <= x ->
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
  refine fun q hq phi hPhi x hx => ?_
  by_cases hZero : x = 0
  · exact Kyprianou.Ch03.firstPassageTransform_positiveDiscount_zeroBarrier
      P F L hNotDecreasing q hq phi hPhi x hZero
  · have hPos : 0 < x := lt_of_le_of_ne hx (Ne.symm hZero)
    exact Kyprianou.Ch03.firstPassageTransform_positiveDiscount_strictBarrier
      P F L hNotDecreasing q hq phi hPhi x hPos
