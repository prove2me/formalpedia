-- Prove2me | solution 1 for IsCyclotomicExtension.Rat.prime_dvd_discr_dvd_conductor
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-20T16:57:21.457901+00:00
-- url     : https://prove2.me/submissions/7e343652-c973-490f-894c-23c4214b5ad7

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

set_option autoImplicit false
noncomputable section

theorem _root_.solution
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K]
    {l : ℕ} (hl : l.Prime)
    (hldisc : (l : ℤ) ∣ NumberField.discr K) : l ∣ n := by
  have hnat : l ∣ (NumberField.discr K).natAbs :=
    Int.natAbs_dvd_natAbs.mpr hldisc
  rw [IsCyclotomicExtension.Rat.natAbs_discr n K] at hnat
  have hden :
      (∏ q ∈ n.primeFactors, q ^ (Nat.totient n / (q - 1))) ∣
        n ^ Nat.totient n :=
    Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos n)
  have hpow : l ∣ n ^ Nat.totient n :=
    hnat.trans (Nat.div_dvd_of_dvd hden)
  exact hl.dvd_of_dvd_pow hpow
