-- Prove2me | solution 1 for Kyprianou.Ch04.bvPathJumpMeasureIntegralEqTsumV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:59:48.200589+00:00
-- url     : https://prove2.me/submissions/f149c8c7-97e3-41db-8f04-b7de46c31265

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_bvPositiveJumpSupportCountableV1
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
import Theorems.Thm_Kyprianou_Ch04_bvRestrictedDiracIntegralV1
import Theorems.Thm_Kyprianou_Ch04_bvHorizonJumpSeriesReindexV1
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
    (t : NNReal) :
    (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega))
          ∂(pathJumpMeasure X Xleft omega)) =
        (∑' s : Set.Ioc (0 : NNReal) t,
          (f (((s : NNReal) : Real), X s omega) -
            f (((s : NNReal) : Real), Xleft s omega))) := by
  have hJ := bvPositiveJumpSupportCountableV1 X Xleft omega (fun u => (hRep u).1)
  letI : Countable {s : NNReal | 0 < s ∧ X s omega ≠ Xleft s omega} := hJ.to_subtype
  let J : Set NNReal := {s | 0 < s ∧ X s omega ≠ Xleft s omega}
  let φ : J → ℝ × ℝ := fun s => (((s : NNReal) : ℝ), X s omega - Xleft s omega)
  let B : Set (ℝ × ℝ) := Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) Set.univ
  let g : ℝ × ℝ → ℝ := fun z =>
    f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
      f (z.1, Xleft (Real.toNNReal z.1) omega)
  rw [bvPathJumpMeasureAtomicV1 X Xleft omega hJ]
  change (∫ z in B, g z ∂(Measure.sum fun s : J => Measure.dirac (φ s))) = _
  exact (bvRestrictedDiracIntegralV1 φ B (measurableSet_Icc.prod MeasurableSet.univ) g).trans
    (bvHorizonJumpSeriesReindexV1 X Xleft omega f t)
