-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfRepeatedOutsideCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:02:48.029956+00:00
-- url     : https://prove2.me/submissions/8583ff10-acb2-4da0-b942-2ba534907624

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfOneDisjointCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (B : Set E) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFiniteB : n B < ⊤) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
        {v : NNReal | 0 < v ∧ 0 < N omega v A})
    ∀ (t u : NNReal) (k l : Nat),
      P {omega | (t : WithTop NNReal) < sigma omega ∧ N omega u B = k ∧ N omega u B = l} =
      P {omega | (t : WithTop NNReal) < sigma omega} *
        P {omega | N omega u B = k ∧ N omega u B = l}
 := by
  dsimp only
  intro t u k l
  by_cases hkl : k = l
  · subst l
    have hSingle :=
      Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
        P n N A firstMark hPPP hA hFinite hMark
        B hB hAB hFiniteB
    dsimp only at hSingle
    simpa only [and_self] using hSingle t u k
  · have hImpossible : ∀ omega : Omega,
        ¬ (N omega u B = k ∧ N omega u B = l) := by
      intro omega hCounts
      exact hkl (hCounts.1.symm.trans hCounts.2)
    have hEmpty : {omega | N omega u B = k ∧ N omega u B = l} = ∅ := by
      ext omega
      simp [hImpossible omega]
    have hEventEmpty :
        {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
          N omega u B = k ∧ N omega u B = l} = ∅ := by
      ext omega
      simp [hImpossible omega]
    rw [hEmpty, hEventEmpty]
    simp
