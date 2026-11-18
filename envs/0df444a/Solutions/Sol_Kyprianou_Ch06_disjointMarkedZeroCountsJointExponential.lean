-- Prove2me | solution 1 for Kyprianou.Ch06.disjointMarkedZeroCountsJointExponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:06:43.996993+00:00
-- url     : https://prove2.me/submissions/59e1f0e4-f3cd-41e4-956c-76880faecbbe

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonCountIndependence
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
import Theorems.Thm_Kyprianou_Ch06_poissonZeroCountAsExponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (s t : NNReal) :
    P {omega | N omega s B = 0 ∧ N omega t D = 0} =
      ENNReal.ofReal
        (Real.exp (-(((n B).toNNReal : Real) * (s : Real)))) *
      ENNReal.ofReal
        (Real.exp (-(((n D).toNNReal : Real) * (t : Real)))) := by
  rw [Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
        P n N hPPP B D hB hD hBD hFB hFD s t 0 0,
      Kyprianou.Ch06.markedPoissonMarginalCountLaw
        P n N hPPP s B hB hFB 0,
      Kyprianou.Ch06.markedPoissonMarginalCountLaw
        P n N hPPP t D hD hFD 0,
      Kyprianou.Ch06.poissonZeroCountAsExponential
        (n B).toNNReal s,
      Kyprianou.Ch06.poissonZeroCountAsExponential
        (n D).toNNReal t]
