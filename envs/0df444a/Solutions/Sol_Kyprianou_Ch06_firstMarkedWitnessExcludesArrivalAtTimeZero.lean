-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkedWitnessExcludesArrivalAtTimeZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:30:59.166206+00:00
-- url     : https://prove2.me/submissions/f2f53638-edaa-4a93-98f4-a06af6c3ca79

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
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
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal := sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    ∀ᵐ omega ∂P, (0 : WithTop NNReal) <
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) := by
  filter_upwards [hPPP.2.1, hMark] with omega hPath hWitness
  let sigma : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 0 < t ∧ 0 < N omega t A})
  change (0 : WithTop NNReal) < sigma
  have hZero : sigma ≠ (0 : WithTop NNReal) := by
    intro hz
    have hFinite : sigma ≠ ⊤ := by
      rw [hz]
      simp
    obtain ⟨x, _, _, hPositive⟩ := hWitness.2 hFinite
    have ht : sigma.untopD 0 = 0 := by
      rw [hz]
      exact WithTop.untopD_coe 0 0
    rw [ht, hPath.1 {x}] at hPositive
    exact Nat.not_lt_zero _ hPositive
  exact lt_of_le_of_ne bot_le (Ne.symm hZero)
