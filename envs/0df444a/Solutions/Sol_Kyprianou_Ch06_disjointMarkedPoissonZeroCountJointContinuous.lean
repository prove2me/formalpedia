-- Prove2me | solution 1 for Kyprianou.Ch06.disjointMarkedPoissonZeroCountJointContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:26:13.643549+00:00
-- url     : https://prove2.me/submissions/7f476f0c-e376-40a5-ac3b-7b50047661ef

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonCountIndependence
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
import Theorems.Thm_Kyprianou_Ch06_poissonZeroCountAsExponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (t u : NNReal) (k : Nat) :
    ContinuousAt (fun s : NNReal =>
      P {omega | N omega s A = 0 ∧ N omega u B = k}) t := by
  let c : ENNReal := P {omega | N omega u B = k}
  have hc : c < ⊤ := by
    have hbound : c ≤ (1 : ENNReal) := by
      simpa [c, measure_univ] using
        (measure_mono (μ := P) (Set.subset_univ {omega | N omega u B = k}))
    exact lt_of_le_of_lt hbound (by simp)
  have hSurv : Continuous (fun s : NNReal =>
      ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real))))) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hMult : Continuous (fun x : ENNReal => x * c) := by
    exact ENNReal.continuous_mul_const (ne_of_lt hc)
  have hCont : Continuous (fun s : NNReal =>
      ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real)))) * c) :=
    hMult.comp hSurv
  have hEq : (fun s : NNReal =>
      P {omega | N omega s A = 0 ∧ N omega u B = k}) =
      (fun s : NNReal =>
      ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real)))) * c) := by
    funext s
    calc
      P {omega | N omega s A = 0 ∧ N omega u B = k} =
          P {omega | N omega s A = 0} * c := by
        exact Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
          P n N hPPP A B hA hB hAB hFiniteA hFiniteB s u 0 k
      _ = ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real)))) * c := by
        rw [Kyprianou.Ch06.markedPoissonMarginalCountLaw
          P n N hPPP s A hA hFiniteA 0]
        rw [Kyprianou.Ch06.poissonZeroCountAsExponential
          (n A).toNNReal s]
        simp [ENNReal.toReal]
  rw [hEq]
  exact hCont.continuousAt
