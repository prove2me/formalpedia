-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkedPoissonZeroIntensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:42:14.357602+00:00
-- url     : https://prove2.me/submissions/e59b935f-11aa-4394-bad0-21d7f08fa903

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonZeroRateCemetery
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
    (n A = 0 →
      P {omega | sigma omega = ⊤ ∧ firstMark omega = none} = 1) := by
  exact Kyprianou.Ch06.markedPoissonZeroRateCemetery P n N A firstMark hPPP hA hFinite hMark

