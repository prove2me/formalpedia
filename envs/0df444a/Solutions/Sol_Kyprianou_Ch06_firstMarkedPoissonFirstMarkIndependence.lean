-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkedPoissonFirstMarkIndependence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:43:17.347347+00:00
-- url     : https://prove2.me/submissions/4e639086-ff38-482e-9788-9c6a2780fcff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_positiveFirstMarkDisjointSupportCase
import Theorems.Thm_Kyprianou_Ch06_markedPoissonPositiveRateFirstMarkIntersectingCase
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open Kyprianou.Ch06
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Lemma 6.18: the first A-mark time is exponential; restriction to
marks outside A has the un-killed Poisson law and is independent of
the killing time; the first A-mark is independent of that stopped
restricted process. The first-mark assertion assumes positive intensity,
since an A-mark does not exist when n(A)=0. -/
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
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (0 < n A →
      ∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat)
      (t : NNReal) (C : Set E),
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
      MeasurableSet C →
        P {omega | firstMark omega ∈ (some '' C) ∧
          (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          ((n (C ∩ A)) / n A) *
            P {omega | (t : WithTop NNReal) < sigma omega ∧
              (∀ i : Fin m, N omega (times i) (B i) = counts i)}) := by
  intro sigma hPos m times B counts t C hB hC
  by_cases hDisj : Disjoint C A
  · exact Kyprianou.Ch06.positiveFirstMarkDisjointSupportCase
      P n N A firstMark hPPP hA hFinite hMark hPos
      m times B counts t C hDisj hB hC
  · exact Kyprianou.Ch06.markedPoissonPositiveRateFirstMarkIntersectingCase
      P n N A firstMark hPPP hA hFinite hMark hPos
      m times B counts t C hDisj hB hC


