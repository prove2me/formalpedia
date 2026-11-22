-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_prime_gaps_in_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:23.877771+00:00
-- url     : https://prove2.me/submissions/61854d51-204c-44ac-8197-b1440993ed5f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_consecutivePrimes_of_composite_interval
import Theorems.Thm_LongGapsBetweenPrimes_short_translates_with_sieveDelta
import Theorems.Thm_LongGapsBetweenPrimes_coverEta_pos
import Theorems.Thm_LongGapsBetweenPrimes_coverEta_le_one
import Theorems.Thm_LongGapsBetweenPrimes_eventually_coverLength_bounds
import Theorems.Thm_LongGapsBetweenPrimes_eventually_covering_residues

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ (q : ℝ) ≤ Real.exp (8 * x) ∧
      (coverEta / 2) * coverScale x ≤ ((q - p : ℕ) : ℝ) := by
  classical
  filter_upwards [eventually_covering_residues,
    eventually_coverLength_bounds coverEta_pos coverEta_le_one,
    short_translates_with_sieveDelta, Filter.eventually_ge_atTop (2 : ℝ)]
    with x hcover hlength htranslate hx
  let H := coverLength coverEta x
  let Q := primorial ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨a, ha, hcard⟩ := hcover
  have hcop : (↑⌊x⌋₊.primesLE : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.mem_primesLE.mp hp).2
      (Nat.mem_primesLE.mp hq).2).mpr hpq
  let b := Nat.chineseRemainderOfFinset (fun p => p - a p) (fun p => p) ⌊x⌋₊.primesLE
    (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero) hcop
  have hb : b.val < Q := by
    simpa only [Q, primorial_eq_prod_primesLE] using
      Nat.chineseRemainderOfFinset_lt_prod (fun p => p - a p) (fun p => p)
        (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero) hcop
  obtain ⟨t, ht, htbound, htcomposite⟩ := htranslate H hlength.1 hlength.2.1
    (survivors (Finset.Icc 1 H) ⌊x⌋₊.primesLE a) (Finset.filter_subset _ _) hcard b.val hb
  let N := b.val + Q * t
  have hQN : Q ≤ N := (Nat.le_mul_of_pos_right Q ht).trans (Nat.le_add_left _ _)
  have hQ2 : 2 ≤ Q := Nat.le_of_dvd (primorial_pos _)
    (Nat.prime_two.dvd_primorial_iff.mpr (Nat.le_floor hx))
  have hcomposite : ∀ s ∈ Finset.Icc 1 H, ¬Nat.Prime (N + s) := by
    intro s hs
    by_cases hsurvives : s ∈ survivors (Finset.Icc 1 H) ⌊x⌋₊.primesLE a
    · exact htcomposite s hsurvives
    · obtain ⟨p, hp, hsp⟩ : ∃ p ∈ ⌊x⌋₊.primesLE, s % p = a p := by
        simpa [survivors, hs] using hsurvives
      obtain ⟨hpx, hpprime⟩ := Nat.mem_primesLE.mp hp
      have hpQ : p ∣ Q := hpprime.dvd_primorial_iff.mpr hpx
      have hbs : p ∣ b.val + s := by
        apply Nat.dvd_of_mod_eq_zero
        calc
          (b.val + s) % p = ((p - a p) + a p) % p := by
            rw [Nat.add_mod, b.property p hp, hsp, Nat.add_mod (p - a p),
              Nat.mod_eq_of_lt (ha p hp)]
          _ = 0 := by rw [Nat.sub_add_cancel (ha p hp).le, Nat.mod_self]
      have hdiv : p ∣ N + s := by
        change p ∣ b.val + Q * t + s
        rw [Nat.add_right_comm]
        exact dvd_add hbs (dvd_mul_of_dvd_left hpQ t)
      have hlt : p < N + s := by
        have := Nat.le_of_dvd (primorial_pos _) hpQ
        have := (Finset.mem_Icc.mp hs).1
        omega
      intro hprime
      exact (hprime.eq_one_or_self_of_dvd p hdiv).elim hpprime.ne_one (ne_of_lt hlt)
  obtain ⟨p, q, hpq, _, _, hqN, hgap⟩ :=
    consecutivePrimes_of_composite_interval (hQ2.trans hQN) (H := H) (by
      intro n hNn hnH
      have hs : n - N ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      simpa only [Nat.add_sub_of_le hNn.le] using hcomposite (n - N) hs)
  refine ⟨p, q, hpq, ?_, hlength.2.2.trans (by exact_mod_cast hgap.le)⟩
  have hQbound : (Q : ℝ) ≤ Real.exp (3 * x) := by
    calc
      (Q : ℝ) ≤ (4 : ℝ) ^ ⌊x⌋₊ := by exact_mod_cast primorial_le_four_pow ⌊x⌋₊
      _ ≤ Real.exp 3 ^ ⌊x⌋₊ := by
        gcongr
        linarith [Real.add_one_le_exp (3 : ℝ)]
      _ = Real.exp (3 * (⌊x⌋₊ : ℝ)) := by rw [← Real.exp_nat_mul, mul_comm]
      _ ≤ Real.exp (3 * x) := by gcongr; exact Nat.floor_le hx0
  have hNbound : (N : ℝ) ≤ 2 * Real.exp (4 * x) := by
    calc
      (N : ℝ) = (b.val : ℝ) + (Q : ℝ) * t := by simp only [N, Nat.cast_add, Nat.cast_mul]
      _ ≤ (Q : ℝ) * (1 + Real.exp x) := by
        have hb' : (b.val : ℝ) ≤ Q := by exact_mod_cast hb.le
        nlinarith [mul_le_mul_of_nonneg_left htbound (Nat.cast_nonneg Q)]
      _ ≤ Real.exp (3 * x) * (2 * Real.exp x) :=
        mul_le_mul hQbound (by linarith [Real.one_le_exp hx0])
          (by positivity) (Real.exp_nonneg _)
      _ = 2 * Real.exp (4 * x) := by
        rw [show (4 : ℝ) * x = 3 * x + x by ring, Real.exp_add]
        ring
  calc
    (q : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hqN
    _ ≤ 4 * Real.exp (4 * x) := by linarith
    _ ≤ Real.exp (4 * x) * Real.exp (4 * x) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (4 * x)]
    _ = Real.exp (8 * x) := by rw [← Real.exp_add]; congr 1; ring
end LongGapsBetweenPrimes
