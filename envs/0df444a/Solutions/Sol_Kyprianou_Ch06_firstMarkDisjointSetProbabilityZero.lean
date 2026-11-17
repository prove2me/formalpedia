-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkDisjointSetProbabilityZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:36:24.439199+00:00
-- url     : https://prove2.me/submissions/3bb5e953-408e-4323-9837-aaf663ba7b42

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (C : Set E) (hCA : Disjoint C A) :
    P {omega | firstMark omega ∈ (some '' C)} = 0 := by
  have hNever : ∀ᵐ omega ∂P,
      firstMark omega ∉ (some '' C) := by
    filter_upwards [hMark] with omega hm
    intro hx
    obtain ⟨x, hxC, hxEq⟩ := hx
    let sigma : WithTop NNReal :=
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    change (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E, firstMark omega = some x ∧
        x ∈ A ∧ 0 < N omega (sigma.untopD 0) {x}) at hm
    by_cases hInfinity : sigma = ⊤
    · have hn := hm.1 hInfinity
      simp [hn] at hxEq
    · obtain ⟨y, hyEq, hyA, _⟩ := hm.2 hInfinity
      have hxy : x = y := Option.some.inj (hxEq.trans hyEq)
      have hxA : x ∈ A := by simpa [hxy] using hyA
      exact (Set.disjoint_left.mp hCA) hxC hxA
  have hZero : P {omega | ¬ firstMark omega ∈ (some '' C)}ᶜ = 0 :=
    (MeasureTheory.mem_ae_iff).mp hNever
  have hSet :
      {omega | ¬ firstMark omega ∈ (some '' C)}ᶜ =
      {omega | firstMark omega ∈ (some '' C)} := by
    ext omega
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  rw [hSet] at hZero
  exact hZero
