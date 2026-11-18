-- Prove2me | solution 1 for Kyprianou.Ch06.firstArrivalPartitionedByMarkMembership
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:09:15.600988+00:00
-- url     : https://prove2.me/submissions/6c1348e4-6b95-430a-8496-314edbeb5959

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstMarkedPoissonArrivalUnionMin
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
    (A C : Set E) :
    ∀ᵐ omega ∂P,
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) =
      min
        (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t (A ∩ C)}))
        (sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t (A \ C)})) := by
  have hDisj : Disjoint (A ∩ C) (A \ C) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 hx.2
  have hUnion : A ∩ C ∪ A \ C = A := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  simpa only [hUnion] using
    (Kyprianou.Ch06.firstMarkedPoissonArrivalUnionMin
      P n N hPPP (A ∩ C) (A \ C) hDisj)
