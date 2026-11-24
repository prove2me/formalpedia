-- Prove2me | solution 1 for Kyprianou.Ch03.submultiplicativeMomentsIffLargeJumpIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:20:14.406683+00:00
-- url     : https://prove2.me/submissions/d0628f8d-9487-466f-aefc-731cfe0a1aa7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_submulMoment_forward
import Theorems.Thm_Kyprianou_Ch03_submulMoment_reverse
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
    (g : Real -> Real)
    (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hg_bounded : forall R : Real, 0 <= R ->
      exists M : Real, forall x : Real, abs x <= R -> g x <= M) :
    (IntegrableOn g {x : Real | 1 <= abs x} T.levyMeasure) <->
    (forall (t : NNReal), 0 < t ->
      Integrable (fun omega => g (X t omega)) P) := by
  exact Iff.intro (Kyprianou.Ch03.submulMoment_forward P X hX T hLK g hg hg_meas hg_bounded) (Kyprianou.Ch03.submulMoment_reverse P X hX T hLK g hg hg_meas hg_bounded)

