-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_consequence1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:42:59.125012+00:00
-- url     : https://prove2.me/submissions/3cad4f05-40a2-40d6-a85f-2efd41980d58

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_consequence_positive
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_consequence_zero
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
    forall (q : Real), 0 <= q ->
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
  refine fun q hq => ?_
  by_cases hzero : q = 0
  · exact Kyprianou.Ch03.firstPassageTransform_consequence_zero
      P F L hNotDecreasing q hzero
  · have hpositive : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    exact Kyprianou.Ch03.firstPassageTransform_consequence_positive
      P F L hNotDecreasing q hpositive
