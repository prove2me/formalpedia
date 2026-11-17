-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkOutsideCForcesComplementPointCountAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:18:37.170798+00:00
-- url     : https://prove2.me/submissions/faf2a678-982e-4411-b557-a7ebc5ff2365

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonCountMonotoneInMarksAllTimesAe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (C : Set E) :
    ∀ᵐ omega ∂P,
      firstMark omega ∉ (some '' C) →
      (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})) ≠ ⊤ →
      0 < N omega
        ((sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})).untopD 0)
        (A \ C) := by
  have hSpace :=
    Kyprianou.Ch06.markedPoissonCountMonotoneInMarksAllTimesAe
      P n N hPPP
  filter_upwards [hMark,hSpace] with omega hm hs hOutside hFinite
  let sigma : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 0 < t ∧ 0 < N omega t A})
  change (sigma = ⊤ → firstMark omega = none) ∧
    (sigma ≠ ⊤ → ∃ x : E,
      firstMark omega = some x ∧ x ∈ A ∧
      0 < N omega (sigma.untopD 0) {x}) at hm
  obtain ⟨x,hxSome,hxA,hxCount⟩ := hm.2 hFinite
  have hxNotC : x ∉ C := by
    intro hxC
    exact hOutside ⟨x,hxC,hxSome.symm⟩
  have hSub : ({x} : Set E) ⊆ A \ C := by
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    exact ⟨hxA,hxNotC⟩
  have hCountLe := hs {x} (A \ C) hSub (sigma.untopD 0)
  exact lt_of_lt_of_le hxCount hCountLe
