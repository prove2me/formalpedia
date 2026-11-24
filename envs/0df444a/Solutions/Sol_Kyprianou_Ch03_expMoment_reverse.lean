-- Prove2me | solution 1 for Kyprianou.Ch03.expMoment_reverse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:01:40.784094+00:00
-- url     : https://prove2.me/submissions/d358e4d5-fd5a-48fc-b2db-0d518c27f073

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_expMoment_reverse_positiveTime
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
    (IntegrableOn (fun x : Real => Real.exp (beta * x))
        {x : Real | 1 <= abs x} T.levyMeasure) -> ((forall (t : NNReal),
      Integrable (fun omega => Real.exp (beta * X t omega)) P)) := by
  refine fun hMeasure t => ?_
  have hNonneg : (0 : NNReal) ≤ t := zero_le
  rcases eq_or_lt_of_le hNonneg with hzero | hp
  · have ht : t = 0 := hzero.symm
    subst t
    simp [hX.start_zero]
  · exact Kyprianou.Ch03.expMoment_reverse_positiveTime
      P X hX T hLK beta hMeasure t hp

