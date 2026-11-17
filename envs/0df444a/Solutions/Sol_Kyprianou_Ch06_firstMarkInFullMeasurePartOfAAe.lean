-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkInFullMeasurePartOfAAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:01:19.43621+00:00
-- url     : https://prove2.me/submissions/a8bd1d2c-bff2-48f5-8e75-a53bfad72ad5

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedFirstArrivalFiniteAlmostSurely
import Theorems.Thm_Kyprianou_Ch06_firstMarkInAOfFiniteArrivalAe
import Theorems.Thm_Kyprianou_Ch06_firstMarkAvoidsNullIntensityPart
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
    (hA : MeasurableSet A) (hFinite : n A < ⊤) (hRate : 0 < n A)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (C : Set E) (hC : MeasurableSet C) (hNull : n (A \ C) = 0) :
    ∀ᵐ omega ∂P, firstMark omega ∈ (some '' C) := by
  have hFiniteArrival :=
    Kyprianou.Ch06.markedFirstArrivalFiniteAlmostSurely
      P n N A firstMark hPPP hA hFinite hRate hMark
  have hInA :=
    Kyprianou.Ch06.firstMarkInAOfFiniteArrivalAe
      P N A firstMark hMark hFiniteArrival
  have hSet : (A \ C) ∩ A = A \ C := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hNullIntersect : n ((A \ C) ∩ A) = 0 := by
    rw [hSet]
    exact hNull
  have hAvoidMeasure :=
    Kyprianou.Ch06.firstMarkAvoidsNullIntensityPart
      P n N A firstMark hPPP hA hMark
      (A \ C) (hA.diff hC) hNullIntersect
  have hAvoid : ∀ᵐ omega ∂P,
      firstMark omega ∉ (some '' (A \ C)) := by
    apply (MeasureTheory.mem_ae_iff).2
    have hEvent :
        {omega | ¬ firstMark omega ∈ (some '' (A \ C))}ᶜ =
        {omega | firstMark omega ∈ (some '' (A \ C))} := by
      ext omega
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    rw [hEvent]
    exact hAvoidMeasure
  filter_upwards [hInA, hAvoid] with omega hMarkA hOutside
  obtain ⟨x, hxA, hxMark⟩ := hMarkA
  refine ⟨x, ?_, hxMark⟩
  by_contra hxNotC
  apply hOutside
  exact ⟨x, ⟨hxA, hxNotC⟩, hxMark⟩
