-- Prove2me | solution 1 for Kyprianou.Ch06.positiveMarkedPointBeforeClockMinForcesEarlierRegion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:19:31.691394+00:00
-- url     : https://prove2.me/submissions/9dbbe7c3-88de-465a-845c-de9037239d78

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_Kyprianou_Ch06_positiveSingletonMarkedCountForcesRegionCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (B D : Set E) (t : NNReal) (x : E)
    (ht : 0 < t) (hxB : x ∈ B)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega t (S ∪ T) = N omega t S + N omega t T)
    (hPositive : 0 < N omega t ({x} : Set E))
    (hMin : (t : WithTop NNReal) = min
      (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B})) (sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D})))
    (hNoTie : sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) ≠ sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D})) :
    sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) < sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D}) := by
  have hPositiveB :=
    Kyprianou.Ch06.positiveSingletonMarkedCountForcesRegionCount
      N omega t x B hxB hAdd hPositive
  have hMem :
      (t : WithTop NNReal) ∈
        ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u B}) :=
    Set.mem_image_of_mem _ ⟨ht, hPositiveB⟩
  have hBefore : sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u B}) ≤ (t : WithTop NNReal) :=
    sInf_le hMem
  have hUntil : (t : WithTop NNReal) ≤ sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D}) := by
    rw [hMin]
    exact min_le_right _ _
  exact lt_of_le_of_ne (hBefore.trans hUntil) hNoTie
