-- Prove2me | solution 1 for Kyprianou.Ch06.beforeFirstArrivalImpliesZeroCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:46:57.245681+00:00
-- url     : https://prove2.me/submissions/c443666b-6680-4e26-bc69-c22e0ed18415

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (A : Set E)
    (hInit : N omega 0 A = 0) (t : NNReal)
    (hBefore : (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})) :
    N omega t A = 0 := by
  by_cases ht : t = 0
  · simpa [ht] using hInit
  · by_contra hne
    have htpos : 0 < t :=
      lt_of_le_of_ne (show (0 : NNReal) ≤ t from zero_le) (Ne.symm ht)
    have hcount : 0 < N omega t A :=
      Nat.pos_of_ne_zero hne
    have hmem :
        (t : WithTop NNReal) ∈
          ((fun u : NNReal => (u : WithTop NNReal)) ''
            {u : NNReal | 0 < u ∧ 0 < N omega u A}) :=
      Set.mem_image_of_mem _ ⟨htpos, hcount⟩
    have hle : sInf ((fun u : NNReal =>
        (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u A}) ≤
        (t : WithTop NNReal) :=
      sInf_le hmem
    exact (not_le_of_gt hBefore) hle
