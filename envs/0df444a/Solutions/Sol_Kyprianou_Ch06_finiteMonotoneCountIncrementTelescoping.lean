-- Prove2me | solution 1 for Kyprianou.Ch06.finiteMonotoneCountIncrementTelescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:53:57.808173+00:00
-- url     : https://prove2.me/submissions/d3479af2-5eb7-4c9c-911b-661c166aea62

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution
    (F : Nat → Nat) (hF : Monotone F) (k : Nat) :
    (∑ i ∈ Finset.range k, (F (i + 1) - F i)) = F k - F 0 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h0 : F 0 ≤ F k := hF (Nat.zero_le k)
      have hk : F k ≤ F (k + 1) := hF (Nat.le_succ k)
      omega
