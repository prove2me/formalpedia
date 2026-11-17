-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkInAOfFiniteArrivalAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:50:59.201814+00:00
-- url     : https://prove2.me/submissions/4d6d8504-3c7d-4769-be82-ddbc7a2776eb

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
        0 < N omega (sigma.untopD 0) {x}))
    (hFinite : P {omega |
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) = ⊤} = 0) :
    ∀ᵐ omega ∂P, firstMark omega ∈ (some '' A) := by
  have hNoInfinity : ∀ᵐ omega ∂P,
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) ≠ ⊤ := by
    apply (MeasureTheory.mem_ae_iff).2
    have hSet :
        {omega |
          sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
            {t : NNReal | 0 < t ∧ 0 < N omega t A}) = ⊤} =
        ({omega |
          sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
            {t : NNReal | 0 < t ∧ 0 < N omega t A}) ≠ ⊤} : Set Omega)ᶜ := by
      ext omega
      simp
    rw [← hSet]
    exact hFinite
  filter_upwards [hMark, hNoInfinity] with omega hm hf
  obtain ⟨x, hxMark, hxA, _⟩ := hm.2 hf
  exact ⟨x, hxA, hxMark.symm⟩
