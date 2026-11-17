-- Prove2me | solution 1 for Kyprianou.Ch06.positiveFirstMarkFullMeasureIntersectionCase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:05:40.762375+00:00
-- url     : https://prove2.me/submissions/8352b58c-e627-4c5c-91e5-4188a8fd8e4a

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstMarkInFullMeasurePartOfAAe
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
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (0 < n A →
      ∀ (m : Nat) (times : Fin m → NNReal)
      (B : Fin m → Set E) (counts : Fin m → Nat)
      (t : NNReal) (C : Set E),
      n (A \ C) = 0 →
      (∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤) →
      MeasurableSet C →
        P {omega | firstMark omega ∈ (some '' C) ∧
          (t : WithTop NNReal) < sigma omega ∧
          (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
          ((n (C ∩ A)) / n A) *
            P {omega | (t : WithTop NNReal) < sigma omega ∧
              (∀ i : Fin m, N omega (times i) (B i) = counts i)}) := by
  dsimp only
  intro hRate m times B counts t C hNull hB hC
  have hInC :=
    Kyprianou.Ch06.firstMarkInFullMeasurePartOfAAe
      P n N A firstMark hPPP hA hFinite hRate hMark C hC hNull
  have hEvent :
      P {omega | firstMark omega ∈ (some '' C) ∧
        (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ i : Fin m, N omega (times i) (B i) = counts i)} =
      P {omega | (t : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
        (∀ i : Fin m, N omega (times i) (B i) = counts i)} := by
    apply measure_congr
    filter_upwards [hInC] with omega hMarkC
    exact propext (and_iff_right hMarkC)
  have hSet : (C ∩ A) ∪ (A \ C) = A := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hDisj : Disjoint (C ∩ A) (A \ C) := by
    apply Set.disjoint_left.mpr
    intro x hxCA hxAC
    exact hxAC.2 hxCA.1
  have hEqual : n (C ∩ A) = n A := by
    have hMeasure : n A = n (C ∩ A) + n (A \ C) := by
      calc
        n A = n ((C ∩ A) ∪ (A \ C)) := by rw [hSet]
        _ = n (C ∩ A) + n (A \ C) :=
          measure_union hDisj (hA.diff hC)
    rw [hNull, add_zero] at hMeasure
    exact hMeasure.symm
  have hRatio : n (C ∩ A) / n A = 1 := by
    rw [hEqual]
    exact ENNReal.div_self (ne_of_gt hRate) (ne_of_lt hFinite)
  rw [hEvent, hRatio]
  simp
