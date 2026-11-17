-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalIndependentOfOutsideCylinderWithImpossibleNullCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:12:05.341084+00:00
-- url     : https://prove2.me/submissions/eb171d18-5a0f-4b57-a4d2-9ab48f9105c9

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonZeroIntensityAllCountsVanish
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
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (m : Nat) (times : Fin m → NNReal) (B : Fin m → Set E)
    (counts : Fin m → Nat)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (hBad : ∃ i : Fin m, n (B i) = 0 ∧ 0 < counts i)
    (t : NNReal) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      (∀ j : Fin m, N omega (times j) (B j) = counts j)} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | ∀ j : Fin m,
      N omega (times j) (B j) = counts j} := by
  obtain ⟨i, hZeroIntensity, hPositive⟩ := hBad
  have hZero :=
    Kyprianou.Ch06.markedPoissonZeroIntensityAllCountsVanish
      P n N hPPP (B i) (hB i).1 hZeroIntensity
  have hImpossible : ∀ᵐ omega ∂P,
      ¬ (∀ j : Fin m, N omega (times j) (B j) = counts j) := by
    filter_upwards [hZero] with omega hz hall
    have hc : counts i = 0 := (hall i).symm.trans (hz (times i))
    exact (Nat.ne_of_gt hPositive) hc
  have hNull :
      P {omega | ∀ j : Fin m,
        N omega (times j) (B j) = counts j} = 0 := by
    have hMeasure :
        P ({omega | ¬ ∀ j : Fin m,
          N omega (times j) (B j) = counts j} : Set Omega)ᶜ = 0 :=
      (MeasureTheory.mem_ae_iff).mp hImpossible
    simpa only [Set.compl_setOf, not_not] using hMeasure
  have hSub :
      {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ j : Fin m, N omega (times j) (B j) = counts j)} ⊆
      {omega | ∀ j : Fin m,
        N omega (times j) (B j) = counts j} := by
    intro omega h
    exact h.2
  have hJointNull :
      P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ j : Fin m, N omega (times j) (B j) = counts j)} = 0 := by
    have hle := measure_mono (μ := P) hSub
    rw [hNull] at hle
    exact le_antisymm hle bot_le
  rw [hJointNull, hNull]
  simp
