-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_positiveDiscount_strictBarrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:18:25.757802+00:00
-- url     : https://prove2.me/submissions/752f5931-1606-49d7-b1c0-e090d916b85c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassage_creepingOnFiniteHit
import Theorems.Thm_Kyprianou_Ch03_firstPassage_esscherCapExpectation
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_strictBarrier_fromCap

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Reduction of the positive-discount strict-barrier first-passage transform to three
source-exact lemmas from Kyprianou's Theorem 3.12 argument:
creeping at first passage, stopped Esscher martingale mean-one identity, and the
`T → ∞` dominated-convergence limit.
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
              Real.exp (-phi * x)) := by
  intro q hq phi hphi x hx finiteTime hfin
  have hCreep :
      ∀ᵐ omega ∂P,
        firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ →
          L.X (finiteTime omega) omega = x :=
    firstPassage_creepingOnFiniteHit P F L x hx.le finiteTime hfin
  have hCap : ∀ T : NNReal,
      (∫ omega,
        (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
            finiteTime omega ≤ T
          then Real.exp (phi * x - q * (finiteTime omega : Real))
          else Real.exp (phi * L.X T omega - q * (T : Real))) ∂P) = 1 :=
    fun T =>
      firstPassage_esscherCapExpectation P F L hNotDecreasing q hq phi hphi x hx
        finiteTime hfin T
  exact firstPassageTransform_positiveDiscount_strictBarrier_fromCap
    P F L hNotDecreasing q hq phi hphi x hx finiteTime hfin hCap hCreep
