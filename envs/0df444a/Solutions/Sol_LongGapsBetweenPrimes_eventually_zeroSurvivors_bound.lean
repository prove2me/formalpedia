-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_zeroSurvivors_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:51.550746+00:00
-- url     : https://prove2.me/submissions/e0463ace-33fa-4c1b-888f-adaa6aebed46

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_eventually_cover_parameters
import Theorems.Thm_LongGapsBetweenPrimes_eventually_smooth_count
import Theorems.Thm_LongGapsBetweenPrimes_zeroSurvivors_prime_or_smooth
import Theorems.Thm_LongGapsBetweenPrimes_coverW_large

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → (H : ℝ) ≤ x * Real.log x ^ 2 →
      ((zeroSurvivors x H).card : ℝ) ≤ (Real.log 4 + 2) * H / Real.log x := by
  classical
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  filter_upwards [Filter.eventually_ge_atTop B, eventually_smooth_count,
    eventually_cover_parameters] with x hxB hsmooth hp
  obtain ⟨hx, hL, _, _, _, _, _, _, _⟩ := hp
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  intro H hxH hH
  have hprime := hB (H : ℝ) (hxB.trans hxH)
  rw [Nat.floor_natCast, ← Nat.primesLE_card_eq_primeCounting] at hprime
  have hlog : Real.log x ≤ Real.log (H : ℝ) := Real.log_le_log hx0 hxH
  have hC : 0 < Real.log 4 + 1 := by
    have h := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hprime := hprime.trans (div_le_div_of_nonneg_left (by positivity) hL0 hlog)
  have hsmall : 2 * (H : ℝ) < x * (coverW x : ℝ) := by
    have hw := mul_lt_mul_of_pos_left (coverW_large hL) hx0
    nlinarith
  let smooth : Finset ℕ := (Finset.Icc 1 H).filter
    (fun n => ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x)
  have hsub : zeroSurvivors x H ⊆ H.primesLE ∪ smooth := by
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    rcases zeroSurvivors_prime_or_smooth hx0 hsmall hn with hpn | hsn
    · exact Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hnI).2, hpn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hsn⟩)
  have hcard : ((zeroSurvivors x H).card : ℝ) ≤ (H.primesLE.card : ℝ) + smooth.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le H.primesLE smooth)
  have hsm := hsmooth H hxH smooth (Finset.filter_subset _ _)
    (fun n hn => (Finset.mem_filter.mp hn).2)
  have hpow : Real.log x ≤ Real.log x ^ 3 := by
    have hsq : (1 : ℝ) ≤ Real.log x ^ 2 := one_le_pow₀ (by linarith : 1 ≤ Real.log x)
    have hm := mul_le_mul_of_nonneg_left hsq hL0.le
    nlinarith
  have hdiv : (H : ℝ) / Real.log x ^ 3 ≤ (H : ℝ) / Real.log x :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hL0 hpow
  calc
    _ ≤ (H.primesLE.card : ℝ) + smooth.card := hcard
    _ ≤ (Real.log 4 + 1) * H / Real.log x + (H : ℝ) / Real.log x :=
      add_le_add hprime (hsm.trans hdiv)
    _ = _ := by ring
end LongGapsBetweenPrimes
