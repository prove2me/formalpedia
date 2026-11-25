-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42SupremumChangeOfVariables
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:24:28.419045+00:00
-- url     : https://prove2.me/submissions/51b5fcbc-7806-4efe-a98f-5f45fee09789
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42AvramPathDataV1
import Theorems.Thm_Kyprianou_Ch04_exercise42DeterministicSupremumCalculusV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => L.X s omega)
          (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (f : Real × Real -> Real)
    (hf : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    let supX : NNReal -> Omega -> Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
    ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
      ∃ maxIntegral : Real,
        Tendsto
          (fun n : Nat =>
            ∑ k ∈ Finset.range n,
              let u : NNReal := t * (k : NNReal) / (n : NNReal)
              let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
              fderiv Real f (supX u omega, L.X u omega) (1, 0) *
                (supX v omega - supX u omega))
          atTop (nhds maxIntegral) ∧
        f (supX t omega, L.X t omega) =
          f (supX 0 omega, L.X 0 omega) +
          L.drift *
            (∫ s in Set.Icc (0 : Real) (t : Real),
              fderiv Real f
                (supX (Real.toNNReal s) omega, L.X (Real.toNNReal s) omega)
                (0, 1) ∂volume) +
          maxIntegral +
          (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
              (Set.Iio (0 : Real)),
            (f (supX (Real.toNNReal z.1) omega,
                Xleft (Real.toNNReal z.1) omega + z.2) -
              f (supX (Real.toNNReal z.1) omega,
                Xleft (Real.toNNReal z.1) omega))
            ∂(pathJumpMeasure L.X Xleft omega)) := by
  filter_upwards [exercise42AvramPathDataV1 P F L hBV hd Xleft hLeft]
    with omega h
  exact exercise42DeterministicSupremumCalculusV1 L.X Xleft omega L.drift hd
    (L.X_zero omega) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2 f hf
