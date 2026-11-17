-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkInCForcesIntersectionPointCountAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:18:28.711205+00:00
-- url     : https://prove2.me/submissions/85154f54-db87-45a1-9063-9d7db676b9f1

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
    ∀ᵐ omega ∂P, firstMark omega ∈ (some '' C) →
      0 < N omega
        ((sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})).untopD 0)
        (C ∩ A) := by
  have hSpace :=
    Kyprianou.Ch06.markedPoissonCountMonotoneInMarksAllTimesAe
      P n N hPPP
  filter_upwards [hMark,hSpace] with omega hm hs hx
  obtain ⟨x,hxC,hxSome⟩ := hx
  let sigma : WithTop NNReal :=
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 0 < t ∧ 0 < N omega t A})
  change (sigma = ⊤ → firstMark omega = none) ∧
    (sigma ≠ ⊤ → ∃ y : E,
      firstMark omega = some y ∧ y ∈ A ∧
      0 < N omega (sigma.untopD 0) {y}) at hm
  have hFinite : sigma ≠ ⊤ := by
    intro hInf
    have hn := hm.1 hInf
    rw [hn] at hxSome
    cases hxSome
  obtain ⟨y,hySome,hyA,hyCount⟩ := hm.2 hFinite
  have hxy : x = y := Option.some.inj (hxSome.trans hySome)
  have hyC : y ∈ C := hxy ▸ hxC
  have hSub : ({y} : Set E) ⊆ C ∩ A := by
    intro z hz
    have hzy : z = y := by simpa using hz
    subst z
    exact ⟨hyC,hyA⟩
  have hCountLe := hs {y} (C ∩ A) hSub (sigma.untopD 0)
  exact lt_of_lt_of_le hyCount hCountLe

