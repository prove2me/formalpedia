-- Prove2me | solution 1 for Kyprianou.Ch06.jointEventContinuousFromExponentialFactorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:01:16.533139+00:00
-- url     : https://prove2.me/submissions/111cc5d9-ce72-4f7f-b256-908f12b56d28

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (D : Set Omega) (rate : Real)
    (f : NNReal → Set Omega)
    (hZero : ∀ s : NNReal,
      P (f s) = ENNReal.ofReal (Real.exp (-(rate * (s : Real)))))
    (hJoint : ∀ s : NNReal,
      P ((f s) ∩ D) = P (f s) * P D)
    (t : NNReal) :
    ContinuousAt (fun s : NNReal => P ((f s) ∩ D)) t := by
  let c : ENNReal := P D
  have hc : c < ⊤ := by
    have hbound : c ≤ (1 : ENNReal) := by
      simpa [c, measure_univ] using
        (measure_mono (μ := P) (Set.subset_univ D))
    exact lt_of_le_of_lt hbound (by simp)
  have hSurv : Continuous (fun s : NNReal =>
      ENNReal.ofReal (Real.exp (-(rate * (s : Real))))) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hMult : Continuous (fun x : ENNReal => x * c) := by
    exact ENNReal.continuous_mul_const (ne_of_lt hc)
  have hCont : Continuous (fun s : NNReal =>
      ENNReal.ofReal (Real.exp (-(rate * (s : Real)))) * c) :=
    hMult.comp hSurv
  have hEq : (fun s : NNReal => P ((f s) ∩ D)) =
      (fun s : NNReal =>
        ENNReal.ofReal (Real.exp (-(rate * (s : Real)))) * c) := by
    funext s
    rw [hJoint s, hZero s]
  rw [hEq]
  exact hCont.continuousAt
