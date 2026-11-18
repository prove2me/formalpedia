-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkedWinnerRegionFromCompetingSurvival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:00:41.369387+00:00
-- url     : https://prove2.me/submissions/b8fc64b0-cf49-479b-8324-f4682c243c07

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_Kyprianou_Ch06_beforeFirstArrivalImpliesZeroCount
import Theorems.Thm_Kyprianou_Ch06_positiveSingletonMarkedCountForcesRegionCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (t : NNReal) (x : E)
    (B D : Set E) (hMark : x ∈ B ∪ D)
    (hInitD : N omega 0 D = 0)
    (hAdd : ∀ S T : Set E, Disjoint S T →
      N omega t (S ∪ T) = N omega t S + N omega t T)
    (hPositive : 0 < N omega t ({x} : Set E))
    (hBeforeD : (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u D})) :
    x ∈ B := by
  rcases hMark with hxB | hxD
  · exact hxB
  · have hPositiveD :=
      Kyprianou.Ch06.positiveSingletonMarkedCountForcesRegionCount
        N omega t x D hxD hAdd hPositive
    have hZeroD :=
      Kyprianou.Ch06.beforeFirstArrivalImpliesZeroCount
        N omega D hInitD t hBeforeD
    omega
