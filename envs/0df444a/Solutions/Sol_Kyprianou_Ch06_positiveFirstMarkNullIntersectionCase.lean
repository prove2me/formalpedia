-- Prove2me | solution 1 for Kyprianou.Ch06.positiveFirstMarkNullIntersectionCase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:01:02.358012+00:00
-- url     : https://prove2.me/submissions/05db6c76-9203-4be7-9773-9dd255a41662

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstMarkAvoidsNullIntensityPart
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
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (0 < n A →
      ∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat)
      (t : NNReal) (C : Set E),
      n (C ∩ A) = 0 →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
      MeasurableSet C →
        P {omega | firstMark omega ∈ (some '' C) ∧
          (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          ((n (C ∩ A)) / n A) *
            P {omega | (t : WithTop NNReal) < sigma omega ∧
              (∀ i : Fin m, N omega (times i) (B i) = counts i)}) := by
  dsimp only
  intro hRate m times B counts t C hNull hB hC
  have hMarkZero :=
    Kyprianou.Ch06.firstMarkAvoidsNullIntensityPart
      P n N A firstMark hPPP hA hMark C hC hNull
  have hSub :
      {omega | firstMark omega ∈ (some '' C) ∧
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ i : Fin m, N omega (times i) (B i) = counts i)} ⊆
      {omega | firstMark omega ∈ (some '' C)} := by
    intro omega hx
    exact hx.1
  have hLhs :
      P {omega | firstMark omega ∈ (some '' C) ∧
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ i : Fin m, N omega (times i) (B i) = counts i)} = 0 := by
    have hle := measure_mono (μ := P) hSub
    rw [hMarkZero] at hle
    exact le_antisymm hle bot_le
  rw [hLhs, hNull]
  simp
