-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkInAOnFiniteArrivalAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:45:38.789723+00:00
-- url     : https://prove2.me/submissions/76aeebc3-ba39-47e2-ae87-78b4d3f59af3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    ∀ᵐ omega ∂P,
      (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) ≠ ⊤) →
      firstMark omega ∈ (some '' A) := by
  filter_upwards [hMark] with omega hm hFinite
  obtain ⟨x, hxMark, hxA, _⟩ := hm.2 hFinite
  exact ⟨x, hxA, hxMark.symm⟩
