-- Prove2me | solution 1 for Kyprianou.Ch06.independentEventOfAlmostSureCountableStatistic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:46:24.363896+00:00
-- url     : https://prove2.me/submissions/0859c296-efc0-4fa7-a433-eb60825cd840

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_independentEventOfAeDisjointCountableUnion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Omega I J : Type} [MeasurableSpace Omega] [Countable I]
    (P : Measure Omega) (D : Set Omega) (hD : MeasurableSet D)
    (X : Omega → I) (Y : Omega → J) (f : I → J)
    (hMeas : ∀ i : I, MeasurableSet {omega | X omega = i})
    (hFactor : ∀ i : I,
      P (D ∩ {omega | X omega = i}) =
        P D * P {omega | X omega = i})
    (hAe : ∀ᵐ omega ∂P, Y omega = f (X omega))
    (j : J) :
    P (D ∩ {omega | Y omega = j}) =
      P D * P {omega | Y omega = j} := by
  classical
  let F : I → Set Omega :=
    fun i => if f i = j then {omega | X omega = i} else ∅
  have hFMeas : ∀ i : I, MeasurableSet (F i) := by
    intro i
    by_cases hi : f i = j
    · simpa [F, hi] using hMeas i
    · simp [F, hi]
  have hFDisj : Pairwise (fun i k : I => Disjoint (F i) (F k)) := by
    intro i k hik
    apply Set.disjoint_left.mpr
    intro omega hi hk
    by_cases hfi : f i = j
    · by_cases hfk : f k = j
      · have hxi : X omega = i := by simpa [F,hfi] using hi
        have hxk : X omega = k := by simpa [F,hfk] using hk
        exact hik (hxi.symm.trans hxk)
      · simpa [F,hfk] using hk
    · simpa [F,hfi] using hi
  have hFIndep : ∀ i : I,
      P (D ∩ F i) = P D * P (F i) := by
    intro i
    by_cases hi : f i = j
    · simpa [F,hi] using hFactor i
    · simp [F,hi]
  have hEq : ∀ᵐ omega ∂P,
      (Y omega = j) ↔ omega ∈ ⋃ i : I, F i := by
    filter_upwards [hAe] with omega heq
    constructor
    · intro hy
      have hf : f (X omega) = j := by
        rw [← heq]
        exact hy
      apply Set.mem_iUnion.mpr
      exact ⟨X omega, by simp [F,hf]⟩
    · intro h
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      by_cases hfi : f i = j
      · have hxi : X omega = i := by
          simpa [F,hfi] using hi
        rw [heq,hxi,hfi]
      · simp [F,hfi] at hi
  exact
    Kyprianou.Ch06.independentEventOfAeDisjointCountableUnion
      P D {omega | Y omega = j} hD F hFMeas hFDisj
      hFIndep hEq
