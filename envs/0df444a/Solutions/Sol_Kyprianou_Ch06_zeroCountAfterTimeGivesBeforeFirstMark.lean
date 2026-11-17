-- Prove2me | solution 1 for Kyprianou.Ch06.zeroCountAfterTimeGivesBeforeFirstMark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:09:41.491991+00:00
-- url     : https://prove2.me/submissions/fd5f9a83-b637-4ca1-b501-e665d10489b6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (omega : Omega)
    (hMono : Monotone (fun t : NNReal => N omega t A))
    (s t : NNReal) (hts : t < s)
    (hZero : N omega s A = 0) :
    (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A}) := by
  have hbound : (s : WithTop NNReal) ≤
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A}) := by
    apply le_sInf
    rintro b ⟨u, ⟨hu, hN⟩, rfl⟩
    have hsu : s < u := by
      by_contra hnot
      have hle : N omega u A ≤ N omega s A :=
        hMono (le_of_not_gt hnot)
      simp [hZero] at hle
      omega
    change (s : WithTop NNReal) ≤ (u : WithTop NNReal)
    exact_mod_cast (le_of_lt hsu)
  exact lt_of_lt_of_le (by exact_mod_cast hts) hbound
