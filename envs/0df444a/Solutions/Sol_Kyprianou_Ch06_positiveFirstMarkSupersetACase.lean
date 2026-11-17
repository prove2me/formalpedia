-- Prove2me | solution 1 for Kyprianou.Ch06.positiveFirstMarkSupersetACase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:51:51.113581+00:00
-- url     : https://prove2.me/submissions/578cd143-931f-4f58-a6cb-bdb48bdfa38f

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedFirstArrivalFiniteAlmostSurely
import Theorems.Thm_Kyprianou_Ch06_firstMarkInAOfFiniteArrivalAe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

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
      A ⊆ C →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
      MeasurableSet C →
        P {omega | firstMark omega ∈ (some '' C) ∧
          (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          ((n (C ∩ A)) / n A) *
            P {omega | (t : WithTop NNReal) < sigma omega ∧
              (∀ i : Fin m, N omega (times i) (B i) = counts i)}) := by
  dsimp only
  intro hRate m times B counts t C hAC hB hMeasC
  have hFiniteFirst :=
    Kyprianou.Ch06.markedFirstArrivalFiniteAlmostSurely
      P n N A firstMark hPPP hA hFinite hRate hMark
  have hSupport :=
    Kyprianou.Ch06.firstMarkInAOfFiniteArrivalAe
      P N A firstMark hMark hFiniteFirst
  have hEvent :
      P {omega | firstMark omega ∈ (some '' C) ∧
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
      P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ i : Fin m, N omega (times i) (B i) = counts i)} := by
    apply measure_congr
    filter_upwards [hSupport] with omega hSupp
    change (firstMark omega ∈ (some '' C) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      (∀ i : Fin m, N omega (times i) (B i) = counts i)) =
      ((t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      (∀ i : Fin m, N omega (times i) (B i) = counts i))
    apply propext
    constructor
    · exact And.right
    · intro hR
      obtain ⟨x, hxA, hxEq⟩ := hSupp
      exact ⟨⟨x, hAC hxA, hxEq⟩, hR⟩
  have hInter : C ∩ A = A := Set.inter_eq_right.mpr hAC
  rw [hEvent, hInter]
  rw [ENNReal.div_self (ne_of_gt hRate) (ne_of_lt hFinite)]
  simp
