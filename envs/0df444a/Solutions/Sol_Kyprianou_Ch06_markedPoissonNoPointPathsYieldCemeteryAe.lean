-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonNoPointPathsYieldCemeteryAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:50:40.394682+00:00
-- url     : https://prove2.me/submissions/f1050a19-3460-4c32-893b-456e54c67c24

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
    (hNoPoints : ∀ᵐ omega ∂P, ∀ t : NNReal, N omega t A = 0) :
    ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      sigma = ⊤ ∧ firstMark omega = none := by
  filter_upwards [hMark, hNoPoints] with omega hm hn
  have hempty : {t : NNReal | 0 < t ∧ 0 < N omega t A} = ∅ := by
    ext t
    simp [hn t]
  have hsigma :
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) = ⊤ := by
    simp only [hempty, Set.image_empty, sInf_empty]
  exact ⟨hsigma, hm.1 hsigma⟩
