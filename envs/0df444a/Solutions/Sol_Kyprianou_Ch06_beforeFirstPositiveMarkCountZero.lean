-- Prove2me | solution 1 for Kyprianou.Ch06.beforeFirstPositiveMarkCountZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:09:34.280877+00:00
-- url     : https://prove2.me/submissions/c5a2d238-232f-4e71-b9e6-9755bb6176d5

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
    (hzero : N omega 0 A = 0)
    (t : NNReal)
    (hBefore : (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})) :
    N omega t A = 0 := by
  by_cases ht : t = 0
  · simpa [ht] using hzero
  · have htpos : 0 < t := lt_of_le_of_ne (zero_le) (Ne.symm ht)
    by_contra hne
    have hpositive : 0 < N omega t A := Nat.pos_of_ne_zero hne
    have hmem :
        (t : WithTop NNReal) ∈
          ((fun u : NNReal => (u : WithTop NNReal)) ''
            {u : NNReal | 0 < u ∧ 0 < N omega u A}) := by
      exact ⟨t, ⟨htpos, hpositive⟩, rfl⟩
    have hle :
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A}) ≤
          (t : WithTop NNReal) := sInf_le hmem
    exact (not_lt_of_ge hle) hBefore
