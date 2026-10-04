-- Prove2me | solution 1 for MertensCorrection.prime_correction_tail_half_bound
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-10-03T18:03:45.441438+00:00
-- url     : https://prove2.me/submissions/4ef33641-2111-47fb-92df-8a712266f7dc

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false

open Finset Real
open scoped BigOperators

namespace MertensTailProof

/-- The convergent correction separating the prime harmonic sum from the logarithm
of the finite Euler product. The prime gate excludes the singular terms at zero and one. -/
noncomputable def correction (n : ℕ) : ℝ :=
  if n.Prime then Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ) else 0

theorem correction_nonpos (n : ℕ) : correction n ≤ 0 := by
  unfold correction
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hp : 0 < 1 - 1 / (n : ℝ) := by
      have : 1 / (n : ℝ) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      linarith
    have := Real.log_le_sub_one_of_pos hp
    linarith
  · exact le_rfl

theorem correction_abs_le (n : ℕ) : |correction n| ≤ 2 / (n : ℝ) ^ 2 := by
  unfold correction
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hn0 : (0 : ℝ) < n := by positivity
    have hu : |1 / (n : ℝ)| < 1 := by
      rw [abs_of_pos (by positivity)]
      exact (div_lt_one hn0).2 (by linarith)
    have h := Real.abs_log_sub_add_sum_range_le hu 1
    simp only [sum_range_one, zero_add, pow_one,
      abs_of_pos (show 0 < 1 / (n : ℝ) by positivity)] at h
    have hden : 0 < 1 - 1 / (n : ℝ) := by
      have : 1 / (n : ℝ) < 1 := (div_lt_one hn0).2 (by linarith)
      linarith
    have hsmall : (1 / (n : ℝ)) ^ 2 / (1 - 1 / (n : ℝ)) ≤ 2 / (n : ℝ) ^ 2 := by
      apply (div_le_iff₀ hden).2
      field_simp
      nlinarith
    calc
      |Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)| ≤
          (1 / (n : ℝ)) ^ 2 / (1 - 1 / (n : ℝ)) := by simpa [add_comm] using h
      _ ≤ 2 / (n : ℝ) ^ 2 := hsmall
  · simp only [abs_zero]
    positivity

theorem summable_correction : Summable correction := by
  have hs : Summable (fun n : ℕ => 2 / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      (summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left (2 : ℝ)
  exact (hs.of_nonneg_of_le (fun n => abs_nonneg (correction n)) correction_abs_le).of_abs

theorem correction_tsum_le_partial (N : ℕ) :
    (∑' n : ℕ, correction n) ≤ ∑ p ∈ Nat.primesLE N,
      (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
  have h := summable_correction.neg.sum_le_tsum (Nat.primesLE N)
    (fun n _ => neg_nonneg.mpr (correction_nonpos n))
  rw [tsum_neg, sum_neg_distrib] at h
  have heq : ∑ p ∈ Nat.primesLE N, correction p =
      ∑ p ∈ Nat.primesLE N, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    apply sum_congr rfl
    intro p hp
    simp [correction, Nat.prime_of_mem_primesLE hp]
  rw [heq] at h
  linarith

theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - x⁻¹) / 2 := by
  let f : ℝ → ℝ := fun t => (t - t⁻¹) / 2 - Real.log t
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt f ((t - 1) ^ 2 / (2 * t ^ 2)) t := by
    apply ((((hasDerivAt_id t).sub ((hasDerivAt_id t).inv (ne_of_gt ht))).div_const 2).sub
      (Real.hasDerivAt_log (ne_of_gt ht))).congr_deriv
    dsimp
    field_simp
    ring
  have hm : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 : ℝ))
      (fun t ht => (hd t (by have ht' := Set.mem_Ici.mp ht; linarith)).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by have ht' := Set.mem_Ici.mp (interior_subset ht); linarith)).hasDerivWithinAt)
    intro t ht
    positivity
  have h := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  dsimp [f] at h
  simp only [inv_one, sub_self, zero_div, Real.log_one] at h
  linarith

/-- The factor one half is retained in the quadratic logarithm remainder. -/
theorem log_correction_sharp {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    -(Real.log (1 - u) + u) ≤ u ^ 2 / (2 * (1 - u)) := by
  have hpos : 0 < 1 - u := by linarith
  have hi : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ hpos).2 (by linarith)
  have h := log_le_half_sub_inv hi
  rw [Real.log_inv, inv_inv] at h
  have heq : ((1 - u)⁻¹ - (1 - u)) / 2 - u = u ^ 2 / (2 * (1 - u)) := by
    field_simp
    ring
  linarith

theorem neg_correction_le_half_telescoping (n : ℕ) (hn : 2 ≤ n) :
    -correction n ≤ 1 / (2 * ((n : ℝ) - 1)) - 1 / (2 * (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have hden : 0 < (n : ℝ) - 1 := by linarith
  unfold correction
  split_ifs with hp
  · have h := log_correction_sharp (show 0 ≤ 1 / (n : ℝ) by positivity)
      ((div_lt_one hn0).2 (by linarith))
    have heq : (1 / (n : ℝ)) ^ 2 / (2 * (1 - 1 / (n : ℝ))) =
        1 / (2 * ((n : ℝ) - 1)) - 1 / (2 * (n : ℝ)) := by
      field_simp
      ring
    rwa [heq] at h
  · simp only [neg_zero, sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem correction_tail_sharp (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : ℕ, -correction (n + (N + 1))) ≤ 1 / (2 * (N : ℝ)) := by
  apply Real.tsum_le_of_sum_range_le
    (fun n => neg_nonneg.mpr (correction_nonpos _))
  intro k
  calc
    ∑ n ∈ range k, -correction (n + (N + 1)) ≤
        ∑ n ∈ range k, (1 / (2 * ((n : ℝ) + N)) -
          1 / (2 * ((n : ℝ) + N + 1))) := by
      apply sum_le_sum
      intro n hn
      have h := neg_correction_le_half_telescoping (n + (N + 1)) (by omega)
      norm_num only [Nat.cast_add, Nat.cast_one] at h
      convert h using 1 <;> congr 2 <;> ring
    _ = 1 / (2 * (N : ℝ)) - 1 / (2 * ((k : ℝ) + N)) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, add_assoc,
        add_comm 1 (N : ℝ)] using
        sum_range_sub' (fun n : ℕ => 1 / (2 * ((n : ℝ) + N))) k
    _ ≤ 1 / (2 * (N : ℝ)) := sub_le_self _ (by positivity)

theorem correction_partial_sub_tsum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ Nat.primesLE N, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
        (∑' n : ℕ, correction n) ≤ 1 / (2 * (N : ℝ)) := by
  have hpartial : (∑ p ∈ Nat.primesLE N,
      (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) =
      ∑ n ∈ range (N + 1), correction n := by
    rw [Nat.primesLE_eq_filter_range, sum_filter]
    rfl
  rw [hpartial]
  have hsum := summable_correction.sum_add_tsum_nat_add (N + 1)
  have htail := correction_tail_sharp N hN
  rw [tsum_neg] at htail
  linarith

theorem tsum_correction_eq_primes :
    (∑' n : ℕ, correction n) =
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
  have h := (tsum_subtype {n : ℕ | n.Prime}
    (fun n : ℕ => Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ))).symm
  convert h using 1
  · apply tsum_congr
    intro n
    simp [correction, Set.indicator]
  · apply tsum_congr
    intro p
    rfl

/-- Both sides of the correction tail, in the prime-subtype convention used by
the Mertens constant. This sharpens the elementary telescoping bound from `1/N`
to `1/(2N)` by retaining the quadratic Taylor coefficient. -/
theorem prime_correction_tail_bounds (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ (∑ p ∈ Nat.primesLE N, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ∧
    (∑ p ∈ Nat.primesLE N, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (2 * (N : ℝ)) := by
  rw [← tsum_correction_eq_primes]
  exact ⟨sub_nonneg.mpr (correction_tsum_le_partial N), correction_partial_sub_tsum_le N hN⟩

end MertensTailProof

theorem solution (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ (∑ p ∈ Nat.primesLE N, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ∧
    (∑ p ∈ Nat.primesLE N, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      1 / (2 * (N : ℝ)) := by
  exact MertensTailProof.prime_correction_tail_bounds N hN
