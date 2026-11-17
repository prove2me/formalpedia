-- Prove2me | solution 1 for Kyprianou.Ch06.twoOutsideJointZeroCountContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:40:28.149279+00:00
-- url     : https://prove2.me/submissions/2afb71b4-6ea9-4fa5-b142-746bf8ab4850

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_threeDisjointMarkedPoissonCountIndependence
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
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u v : NNReal) (k l : Nat) :
    ContinuousAt (fun s : NNReal =>
      P {omega | N omega s A = 0 ∧ N omega u B = k ∧
        N omega v C = l}) t := by
  let c : ENNReal :=
    P {omega | N omega u B = k ∧ N omega v C = l}
  have hc : c < ⊤ := by
    have hBound : c ≤ (1 : ENNReal) := by
      simpa [c, measure_univ] using
        (measure_mono (μ := P)
          (Set.subset_univ {omega |
            N omega u B = k ∧ N omega v C = l}))
    exact lt_of_le_of_lt hBound (by simp)
  have hSurv : Continuous (fun s : NNReal =>
      ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real))))) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hMult : Continuous (fun x : ENNReal => x * c) := by
    exact ENNReal.continuous_mul_const (ne_of_lt hc)
  have hCont : Continuous (fun s : NNReal =>
      ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real)))) * c) :=
    hMult.comp hSurv
  have hEq : (fun s : NNReal =>
      P {omega | N omega s A = 0 ∧ N omega u B = k ∧
        N omega v C = l}) =
      (fun s : NNReal =>
       ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real)))) * c) := by
    funext s
    have hTriple :=
      Kyprianou.Ch06.threeDisjointMarkedPoissonCountIndependence
        P n N hPPP A B C hA hB hC hAB hAC hBC
        hFA hFB hFC s u v 0 k l
    have hTwo :=
      Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
        P n N hPPP B C hB hC hBC hFB hFC u v k l
    calc
      P {omega | N omega s A = 0 ∧ N omega u B = k ∧
        N omega v C = l} =
        P {omega | N omega s A = 0} *
          (P {omega | N omega u B = k} *
           P {omega | N omega v C = l}) := by
          simpa only [mul_assoc] using hTriple
      _ = P {omega | N omega s A = 0} * c := by
        simp only [c, hTwo]
      _ = ENNReal.ofReal (Real.exp (-((n A).toReal * (s : Real)))) * c := by
        rw [Kyprianou.Ch06.markedPoissonMarginalCountLaw
          P n N hPPP s A hA hFA 0]
        rw [Kyprianou.Ch06.poissonZeroCountAsExponential
          (n A).toNNReal s]
        simp [ENNReal.toReal]
  rw [hEq]
  exact hCont.continuousAt
