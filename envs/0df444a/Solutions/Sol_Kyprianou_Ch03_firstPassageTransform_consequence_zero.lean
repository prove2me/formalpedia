-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_consequence_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:09:54.126193+00:00
-- url     : https://prove2.me/submissions/62052dc0-9c1f-446b-96f7-2ecc7adefea7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_zeroDiscount_zeroBarrier
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_zeroDiscount_strictBarrier
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
    forall (q : Real), q = 0 ->
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
  · exact Kyprianou.Ch03.firstPassageTransform_zeroDiscount_zeroBarrier
      P F L hNotDecreasing q hq phi hPhi x hZero
  · have hPos : 0 < x := lt_of_le_of_ne hx (Ne.symm hZero)
    exact Kyprianou.Ch03.firstPassageTransform_zeroDiscount_strictBarrier
      P F L hNotDecreasing q hq phi hPhi x hPos
