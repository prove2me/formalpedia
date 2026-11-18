-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkedPoissonArrivalUnionMin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:52:22.71834+00:00
-- url     : https://prove2.me/submissions/00debdaf-596f-4862-9dbf-03be25796d5e

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
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hDisj : Disjoint B D) :
    ∀ᵐ omega ∂P,
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t (B ∪ D)}) =
      min
        (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t B}))
        (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t D})) := by
  filter_upwards [hPPP.2.1] with omega hPath
  have hEq :
      {t : NNReal | 0 < t ∧ 0 < N omega t (B ∪ D)} =
      {t : NNReal | 0 < t ∧ 0 < N omega t B} ∪
      {t : NNReal | 0 < t ∧ 0 < N omega t D} := by
    ext t
    have hAdd := hPath.2.1 t B D hDisj
    simp only [Set.mem_setOf_eq, Set.mem_union]
    by_cases ht : 0 < t
    · simp only [ht, true_and]
      rw [hAdd]
      omega
    · simp [ht]
  rw [hEq, Set.image_union, sInf_union]
