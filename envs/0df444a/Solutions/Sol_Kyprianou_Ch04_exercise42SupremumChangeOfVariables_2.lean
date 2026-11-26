-- Prove2me | solution 2 for Kyprianou.Ch04.exercise42SupremumChangeOfVariables
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:02:45.453017+00:00
-- url     : https://prove2.me/submissions/21618ed9-66f7-4b76-98d0-9b1f93c36607

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42AvramPathDataV1
import Theorems.Thm_Kyprianou_Ch04_exercise42DeterministicSupremumCalculusV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
open Kyprianou.Ch04
set_option autoImplicit false

/-- Combine original source path data with the deterministic supremum calculus. -/
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
  filter_upwards [Kyprianou.Ch04.exercise42AvramPathDataV1 P F L hBV hd Xleft hLeft] with omega h
  exact Kyprianou.Ch04.exercise42DeterministicSupremumCalculusV1
    L.X Xleft omega L.drift hd (L.X_zero omega) h.1 h.2.1 h.2.2.1
    h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 f hf
