-- Prove2me | solution 1 for Kyprianou.Ch06.twoOutsideZeroCountsAtOrderedTimesAsSeparatedRectanglesAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:27:42.817917+00:00
-- url     : https://prove2.me/submissions/cb49374c-fb09-4efe-8637-48d958b8d7f4

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
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (s t : NNReal) (hst : s ≤ t) :
    ∀ᵐ omega ∂P,
      (N omega s B = 0 ∧ N omega t C = 0) ↔
      (N omega s (B ∪ C) = 0 ∧
       N omega t C - N omega s C = 0) := by
  have hSpace :=
    Kyprianou.Ch06.markedPoissonCountMonotoneInMarksAllTimesAe
      P n N hPPP
  filter_upwards [hPPP.2.1,hSpace] with omega hw hs
  have hDisj : Disjoint B (C \ B) := by
    apply Set.disjoint_left.mpr
    intro x hxB hxCB
    exact hxCB.2 hxB
  have hUnion : B ∪ (C \ B) = B ∪ C := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    tauto
  have hAdd : N omega s (B ∪ C) =
      N omega s B + N omega s (C \ B) := by
    rw [← hUnion]
    exact hw.2.1 s B (C \ B) hDisj
  have hTime : N omega s C ≤ N omega t C :=
    hw.2.2 C hst
  have hBLe : N omega s B ≤ N omega s (B ∪ C) :=
    hs B (B ∪ C) Set.subset_union_left s
  have hCLe : N omega s C ≤ N omega s (B ∪ C) :=
    hs C (B ∪ C) Set.subset_union_right s
  have hDiffLe : N omega s (C \ B) ≤ N omega s C :=
    hs (C \ B) C Set.diff_subset s
  constructor
  · rintro ⟨hB0,hCt0⟩
    constructor <;> omega
  · rintro ⟨hUnion0,hInc0⟩
    constructor <;> omega
