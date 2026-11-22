-- Prove2me | solution 2 for MasulloRH.logDeriv_on_strip_complement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-22T14:30:21.142805+00:00
-- url     : https://prove2.me/submissions/4925c7fc-b72c-4411-8878-e3ff1bfff686
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_prime_height_critical_zero_count_certificates
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Data.Nat.Prime.Infinite

set_option autoImplicit false

open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : InTraceContinuationDomain α s) :
    AnalyticAt ℂ zetaLogDeriv s := by
  obtain ⟨hstrip, hs_one⟩ := hs
  have hright : 1 / 2 < s.re := by linarith
  have hζ := analyticOn_riemannZeta s hs_one
  apply hζ.deriv.div hζ
  by_cases hone : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hone
  intro hz
  let z : ZetaZerosInTraceStrip (1 / 2) :=
    ⟨s, hz, by linarith, lt_of_not_ge hone, abs_lt.mpr ⟨by linarith, by linarith⟩⟩

  -- Choose one certified band containing this particular zero.
  obtain ⟨n, hn⟩ := exists_nat_gt |s.im|
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max 100 n)
  have hp100 : 100 ≤ p := (le_max_left _ _).trans hp
  have hnp : n ≤ p := (le_max_right _ _).trans hp
  have hpow : p ≤ p ^ 6 := le_self_pow (by omega) (by decide)
  have hheight : |s.im| ≤ 5 / 2 + 2 * ((p ^ 6 : ℕ) : ℝ) := by
    have hbound : (n : ℝ) ≤ ((p ^ 6 : ℕ) : ℝ) := by exact_mod_cast hnp.trans hpow
    linarith [Nat.cast_nonneg (α := ℝ) (p ^ 6)]

  obtain ⟨F, hF, hcard⟩ := prime_height_critical_zero_count_certificates p hprime hp100
  let band := {w : ZetaZerosInTraceStrip (1 / 2) |
    |w.val.im| ≤ 5 / 2 + 2 * ((p ^ 6 : ℕ) : ℝ)}
  have hsubset : (F : Set _) ⊆ band := fun w hw => (hF w hw).2
  have hcover : (F : Set _) = band :=
    F.finite_toSet.eq_of_subset_of_encard_le hsubset (by
      simpa only [Set.encard_coe_eq_coe_finsetCard] using hcard)
  have hzF : z ∈ (F : Set _) := hcover.symm ▸ (show z ∈ band from hheight)
  exact (ne_of_gt hright) (hF z hzF).1
