-- Prove2me | solution 1 for Kyprianou.Ch04.bvDeterministicJumpChainRuleV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:41:44.212617+00:00
-- url     : https://prove2.me/submissions/0a5c50e9-a5ba-4306-b979-5d447a17df7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpTruncationIdentityV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpTruncationLimitV1
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureIntegralEqTsumV1
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
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    forall t : NNReal,
      f ((t : Real), X t omega) =
        f (0, X 0 omega) +
        (∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (s, X (Real.toNNReal s) omega)
            (1, 0) ∂volume) +
        c *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            fderiv Real f (s, X (Real.toNNReal s) omega)
              (0, 1) ∂volume) +
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega))
          ∂(pathJumpMeasure X Xleft omega)) := by
  intro t
  have hfinite := bvFiniteJumpTruncationIdentityV1 X Xleft omega c
    hCadlag hLeft hRep f hf t
  obtain ⟨hleft, hright⟩ := bvFiniteJumpTruncationLimitV1 X Xleft omega c
    hCadlag hLeft hRep f hf t
  rw [bvPathJumpMeasureIntegralEqTsumV1 X Xleft omega c hCadlag hLeft hRep f hf t]
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.Eventually.of_forall fun S => (hfinite S).symm))
