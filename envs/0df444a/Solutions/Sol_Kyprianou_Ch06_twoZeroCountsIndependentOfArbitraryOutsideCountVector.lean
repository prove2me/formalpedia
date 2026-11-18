-- Prove2me | solution 1 for Kyprianou.Ch06.twoZeroCountsIndependentOfArbitraryOutsideCountVector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:34:23.937206+00:00
-- url     : https://prove2.me/submissions/736869b0-e018-44e8-a2c5-11af9345e4ed

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_outsideCountVectorCompatibleRectangleRepresentation
import Theorems.Thm_Kyprianou_Ch06_twoZeroCountsIndependentOfFiniteCompatibleRectangleObservable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B D : Set E)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (hBA : B ⊆ A) (hDA : D ⊆ A)
    (m : Nat) (times : Fin m → NNReal)
    (C : Fin m → Set E) (counts : Fin m → Nat)
    (hC : ∀ i, MeasurableSet (C i) ∧
      C i ⊆ Aᶜ ∧ n (C i) < ⊤)
    (s t : NNReal) :
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0 ∧
      (∀ i : Fin m, N omega (times i) (C i) = counts i)} =
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0} *
    P {omega |
      ∀ i : Fin m, N omega (times i) (C i) = counts i} := by
  obtain ⟨k, starts, stops, F, hValid, hAF, hSep, f, hAe⟩ :=
    Kyprianou.Ch06.outsideCountVectorCompatibleRectangleRepresentation
      P n N A hPPP hA hFA m times C hC
  have hBF : ∀ i : Fin k, Disjoint B (F i) := by
    intro i
    exact Set.disjoint_of_subset_left hBA (hAF i)
  have hDF : ∀ i : Fin k, Disjoint D (F i) := by
    intro i
    exact Set.disjoint_of_subset_left hDA (hAF i)
  have h :=
    Kyprianou.Ch06.twoZeroCountsIndependentOfFiniteCompatibleRectangleObservable
      P n N hPPP B D hB hD hBD hFB hFD
      k m starts stops F hValid hBF hDF hSep
      s t
      (fun omega : Omega => fun i : Fin m =>
        N omega (times i) (C i)) f hAe counts
  simpa only [funext_iff, Set.setOf_forall,
    Set.mem_setOf_eq] using h
