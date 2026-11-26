-- Prove2me | solution 2 for Kyprianou.Ch04.exercise49GeneralBvDownwardPersistence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:52:38.802508+00:00
-- url     : https://prove2.me/submissions/df87eb80-5274-402d-aa87-875bcdb3b654

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvSmallTimeDrift
import Theorems.Thm_Kyprianou_Ch04_exercise49PositiveDriftAlmostSurePositivePersistenceV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Apply almost-sure positive persistence to the small-time drift theorem of part (i). -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift =
       triplet.drift -
         ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega))) :
    let tau : Omega -> WithTop NNReal := fun omega =>
      sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t omega < 0};
    0 < P {omega : Omega | 0 < tau omega} := by
  exact Kyprianou.Ch04.exercise49PositiveDriftAlmostSurePositivePersistenceV1
    P X drift hd (Kyprianou.Ch04.exercise49GeneralBvSmallTimeDrift
      P X hLevy triplet hTriplet hBV drift hDrift hd hNotSubordinator)
