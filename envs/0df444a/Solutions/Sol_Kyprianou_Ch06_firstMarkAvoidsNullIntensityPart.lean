-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkAvoidsNullIntensityPart
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:57:10.397233+00:00
-- url     : https://prove2.me/submissions/f3e90c4e-109d-49c1-865e-87c5aed7cefc

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonZeroIntensityAllCountsVanish
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
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (C : Set E) (hC : MeasurableSet C) (hNull : n (C ∩ A) = 0) :
    P {omega | firstMark omega ∈ (some '' C)} = 0 := by
  have hZero :=
    Kyprianou.Ch06.markedPoissonZeroIntensityAllCountsVanish
      P n N hPPP (C ∩ A) (hC.inter hA) hNull
  have hSpace :=
    Kyprianou.Ch06.markedPoissonCountMonotoneInMarksAllTimesAe
      P n N hPPP
  have hNever : ∀ᵐ omega ∂P,
      firstMark omega ∉ (some '' C) := by
    filter_upwards [hMark, hZero, hSpace] with omega hm hz hs
    intro hx
    obtain ⟨x, hxC, hxEq⟩ := hx
    let sigma : WithTop NNReal :=
      sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
        {s : NNReal | 0 < s ∧ 0 < N omega s A})
    change (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ y : E,
        firstMark omega = some y ∧ y ∈ A ∧
        0 < N omega (sigma.untopD 0) {y}) at hm
    by_cases hInf : sigma = ⊤
    · have hn := hm.1 hInf
      simp [hn] at hxEq
    · obtain ⟨y, hyMark, hyA, hyPos⟩ := hm.2 hInf
      have hxy : x = y := Option.some.inj (hxEq.trans hyMark)
      have hyC : y ∈ C := by simpa [hxy] using hxC
      have hSub : ({y} : Set E) ⊆ C ∩ A := by
        intro z hz
        have hzy : z = y := by simpa using hz
        subst z
        exact ⟨hyC, hyA⟩
      have hBound := hs {y} (C ∩ A) hSub (sigma.untopD 0)
      have hZeroAt := hz (sigma.untopD 0)
      omega
  have hMeasure : P {omega | ¬ firstMark omega ∈ (some '' C)}ᶜ = 0 :=
    (MeasureTheory.mem_ae_iff).mp hNever
  have hSet :
      {omega | ¬ firstMark omega ∈ (some '' C)}ᶜ =
      {omega | firstMark omega ∈ (some '' C)} := by
    ext omega
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  rw [hSet] at hMeasure
  exact hMeasure
