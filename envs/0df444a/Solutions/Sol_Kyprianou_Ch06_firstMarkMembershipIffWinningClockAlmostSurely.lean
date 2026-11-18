-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkMembershipIffWinningClockAlmostSurely
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:41:55.63539+00:00
-- url     : https://prove2.me/submissions/879be189-f872-42b7-bf77-de414798797b

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstMarkBelongsToCExactlyWhenCompetingClockWinsAE
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
    (A C : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal := sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (hFinite : ∀ᵐ omega ∂P, sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) ≠ ⊤)
    (hNoTie : ∀ᵐ omega ∂P,
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)}) ≠ sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})) :
    ∀ᵐ omega ∂P,
      (firstMark omega ∈ (some '' C) ↔
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)}) < sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})) := by
  have hBase :=
    Kyprianou.Ch06.firstMarkBelongsToCExactlyWhenCompetingClockWinsAE
      P n N A C firstMark hPPP hMark
  filter_upwards [hPPP.2.1, hMark, hFinite, hNoTie, hBase]
    with omega hPath hWitness hFin hTie hEquiv
  let sigma : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 0 < t ∧ 0 < N omega t A})
  obtain ⟨x, hxMark, hxA, hxPositive⟩ := hWitness.2 hFin
  have hTime : 0 < sigma.untopD 0 := by
    by_contra hNot
    have hz : sigma.untopD 0 = 0 :=
      le_antisymm (not_lt.mp hNot) bot_le
    rw [hz, hPath.1 {x}] at hxPositive
    exact Nat.not_lt_zero _ hxPositive
  have hMembership :
      (firstMark omega ∈ (some '' C)) ↔
        firstMark omega ∈ (some '' (A ∩ C)) := by
    constructor
    · rintro ⟨y, hyC, hyMark⟩
      have heq : y = x :=
        Option.some.inj (by simpa only [hxMark] using hyMark)
      subst y
      exact ⟨x, ⟨hxA, hyC⟩, hxMark.symm⟩
    · rintro ⟨y, hyB, hyMark⟩
      exact ⟨y, hyB.2, hyMark⟩
  exact hMembership.trans (hEquiv hFin hTime hTie)
