-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:53:41.691476+00:00
-- url     : https://prove2.me/submissions/eb186795-ae3a-4e9a-812f-81451b3a0bbe

import Mathlib.RingTheory.MvPowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

theorem solution
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (a : R) (n : ℕ) :
    ∀ k : σ →₀ ℕ,
      MvPowerSeries.coeff k ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) ≠ 0 →
        k ≤ Finsupp.single x n := by
  induction n with
  | zero =>
      intro k hk
      by_cases hzero : k = 0
      · simpa [hzero]
      · simp [MvPowerSeries.coeff_one, hzero] at hk
  | succ n ih =>
      intro k hk
      rw [pow_succ, mul_add, map_add] at hk
      by_cases hXzero :
          MvPowerSeries.coeff k
            ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n * MvPowerSeries.X x) = 0
      · have hC :
            MvPowerSeries.coeff k
              ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n * MvPowerSeries.C a) ≠ 0 := by
              simpa only [hXzero, zero_add] using hk
        have hCcomm :
            (MvPowerSeries.X x + MvPowerSeries.C a) ^ n * MvPowerSeries.C a =
              MvPowerSeries.C a * (MvPowerSeries.X x + MvPowerSeries.C a) ^ n :=
                mul_comm _ _
        rw [hCcomm, MvPowerSeries.coeff_C_mul] at hC
        have hprev :
            MvPowerSeries.coeff k
              ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) ≠ 0 :=
                right_ne_zero_of_mul hC
        exact le_trans (ih k hprev) (Finsupp.single_le_single.mpr (Nat.le_succ n))
      · have hX :
            MvPowerSeries.coeff k
              ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n * MvPowerSeries.X x) ≠ 0 :=
                hXzero
        change
            MvPowerSeries.coeff k
              ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n *
                MvPowerSeries.monomial (Finsupp.single x 1) (1 : R)) ≠ 0 at hX
        by_cases hle : Finsupp.single x 1 ≤ k
        · have hprev :
              MvPowerSeries.coeff (k - Finsupp.single x 1)
                ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) ≠ 0 := by
            simpa [MvPowerSeries.coeff_mul_monomial, hle] using hX
          have hbound := ih (k - Finsupp.single x 1) hprev
          calc
            k = (k - Finsupp.single x 1) + Finsupp.single x 1 := by
              simpa only [add_comm] using (add_tsub_cancel_of_le hle).symm
            _ ≤ Finsupp.single x n + Finsupp.single x 1 := add_le_add hbound le_rfl
            _ = Finsupp.single x (n + 1) := by rw [← Finsupp.single_add]
        · simp [MvPowerSeries.coeff_mul_monomial, hle] at hX
