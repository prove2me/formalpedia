-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassage_esscherCap_trueStoppedMeanOne
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:44:27.192625+00:00
-- url     : https://prove2.me/submissions/2d1f058f-8183-4d81-814d-52a22aaa629d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassage_esscherCapTime_isRightContStoppingTime
import Theorems.Thm_Kyprianou_Ch03_firstPassage_esscherCap_meanOne_of_rightContStoppingTime

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
True stopped Esscher mean-one at `τ_x^+ ∧ T`, reduced to:
1. capped time is an `F.rightCont`-stopping time (bounded by `T`);
2. Esscher mean-one given that stopping-time hypothesis.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : Real) (hq : 0 < q)
    (phi : Real)
    (hRoot : 0 ≤ phi ∧ L.ψ phi = q ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = q → theta ≤ phi))
    (x : Real) (hx : 0 < x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal))
    (T : NNReal) :
    (∫ omega,
      Real.exp (phi *
          (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
              finiteTime omega ≤ T
            then L.X (finiteTime omega) omega
            else L.X T omega)
        - q *
          (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
              finiteTime omega ≤ T
            then (finiteTime omega : Real)
            else (T : Real))) ∂P) = 1 := by
  have _ := hNotDecreasing
  have hStopBound :=
    firstPassage_esscherCapTime_isRightContStoppingTime P F L x hx finiteTime hfin T
  exact firstPassage_esscherCap_meanOne_of_rightContStoppingTime
    P F L q hq phi hRoot x hx finiteTime hfin T hStopBound.1 hStopBound.2
