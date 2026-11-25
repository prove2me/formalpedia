-- Prove2me | solution 1 for Kyprianou.Ch04.bvTruncationDerivativeIntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:38:21.172405+00:00
-- url     : https://prove2.me/submissions/2a46a15c-59b6-422b-bcf6-d5f4dc5f967d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedDerivativeIntegralLimitV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : forall t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (t : NNReal) (v : Real × Real) :
    let jump : Set.Ioc (0 : NNReal) t → Real :=
      fun s => X s omega - Xleft s omega
    let approx : Finset (Set.Ioc (0 : NNReal) t) → NNReal → Real :=
      fun S u => X 0 omega + c * (u : Real) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then jump s else 0
    Tendsto (fun S => ∫ u in Set.Icc (0 : Real) (t : Real),
      fderiv Real f (u, approx S (Real.toNNReal u)) v ∂volume)
      atTop (nhds (∫ u in Set.Icc (0 : Real) (t : Real),
        fderiv Real f (u, X (Real.toNNReal u) omega) v ∂volume)) := by
  exact Kyprianou.Ch04.bvTruncatedDerivativeIntegralLimitV1
    X Xleft omega c hRep hLeft f hf t v
