-- Prove2me | solution 1 for Kyprianou.Ch03.exponentialMomentsIffLargeJumpIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:20:02.018199+00:00
-- url     : https://prove2.me/submissions/723e6dea-fc5f-48e6-9dc7-bffa3cb3fb14

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_expMoment_forward
import Theorems.Thm_Kyprianou_Ch03_expMoment_reverse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real) :
    (forall (t : NNReal),
      Integrable (fun omega => Real.exp (beta * X t omega)) P) <->
      IntegrableOn (fun x : Real => Real.exp (beta * x))
        {x : Real | 1 <= abs x} T.levyMeasure := by
  exact Iff.intro (Kyprianou.Ch03.expMoment_forward P X hX T hLK beta) (Kyprianou.Ch03.expMoment_reverse P X hX T hLK beta)

