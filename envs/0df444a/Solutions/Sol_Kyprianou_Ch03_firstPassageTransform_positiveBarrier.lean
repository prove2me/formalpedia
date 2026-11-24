-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_positiveBarrier
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:59:42.172129+00:00
-- url     : https://prove2.me/submissions/b3075d03-3236-4470-b68c-ac081886bab4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_strictBarrier

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
`firstPassageTransform_positiveBarrier` is definitionally the same quantified statement as the
Proved leaf `firstPassageTransform_positiveDiscount_strictBarrier` (`0 < x` case). Apply it.
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
      (forall (x : Real), 0 < x ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x)) :=
  firstPassageTransform_positiveDiscount_strictBarrier P F L hNotDecreasing
