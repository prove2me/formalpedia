-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkedPoissonOutsideIndependence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:45:57.106459+00:00
-- url     : https://prove2.me/submissions/44b7a23c-d052-490d-81a8-ea3f131e0b2c

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfOneDisjointCount
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalOutsideIndependenceMany
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
    (∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat) (t : NNReal),
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
        P {omega | (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          P {omega | (t : WithTop NNReal) < sigma omega} *
            P {omega |
              ∀ i : Fin m, N omega (times i) (B i) = counts i}) := by
  intro sigma m times B counts t hB
  by_cases hm2 : 2 ≤ m
  · exact Kyprianou.Ch06.markedPoissonArrivalOutsideIndependenceMany
      P n N A firstMark hPPP hA hFinite hMark
      m times B counts t hm2 hB
  · have hm : m < 2 := by omega
    interval_cases m
    · simp
    · obtain ⟨hMeas, hSub, hFin⟩ := hB 0
      have hDisj : Disjoint A (B 0) := by
        apply Set.disjoint_left.mpr
        intro x hxA hxB
        exact hSub hxB hxA
      have hOne :=
        Kyprianou.Ch06.firstArrivalIndependentOfOneDisjointCount
          P n N A firstMark hPPP hA hFinite hMark
          (B 0) hMeas hDisj hFin t (times 0) (counts 0)
      simpa only [Fin.forall_fin_one] using hOne


