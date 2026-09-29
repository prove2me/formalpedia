-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3029bcac-682f-50cc-bc33-2f8ce8efbaa5

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero

set_option autoImplicit false

namespace PairValuesIndependence

private theorem pairValues_heckeRecursionSeq_one_eq_sum (a₁ a₂ : ℂ) (r : ℕ) :
    UnramifiedWhittaker.heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) r =
      ∑ i ∈ Finset.range (r + 1), a₁ ^ i * a₂ ^ (r - i) := by
  have hstep : ∀ r : ℕ,
      (∑ i ∈ Finset.range (r + 1 + 1), a₁ ^ i * a₂ ^ (r + 1 - i)) =
        a₁ * (∑ i ∈ Finset.range (r + 1), a₁ ^ i * a₂ ^ (r - i)) + a₂ ^ (r + 1) := by
    intro r
    rw [Finset.sum_range_succ', Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    · simp
  induction r using Nat.twoStepInduction with
  | zero => simp [UnramifiedWhittaker.heckeRecursionSeq]
  | one =>
    simp only [UnramifiedWhittaker.heckeRecursionSeq, div_one, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, Nat.sub_zero, Nat.sub_self, one_mul, mul_one]
    ring
  | more n ih1 ih2 =>
    rw [UnramifiedWhittaker.heckeRecursionSeq, div_one, ih2, ih1]
    show _ = ∑ i ∈ Finset.range (n + 1 + 1 + 1), a₁ ^ i * a₂ ^ (n + 1 + 1 - i)
    rw [hstep (n + 1), hstep n]
    ring

private theorem pairValues_sum_swap (a₁ a₂ : ℂ) (d : ℕ) (c : ℕ → ℂ) :
    (∑ k ∈ Finset.range (d / 2 + 1),
        (a₁ * a₂) ^ k * (∑ i ∈ Finset.range (d - 2 * k + 1), a₁ ^ i * a₂ ^ (d - 2 * k - i)) * c k) =
      ∑ m ∈ Finset.range (d + 1),
        (∑ k ∈ Finset.range (min m (d - m) + 1), c k) * a₁ ^ m * a₂ ^ (d - m) := by
  have h1 : ∀ k ∈ Finset.range (d / 2 + 1),
      (a₁ * a₂) ^ k * (∑ i ∈ Finset.range (d - 2 * k + 1), a₁ ^ i * a₂ ^ (d - 2 * k - i)) * c k =
        ∑ m ∈ Finset.Ico k (d - k + 1), c k * a₁ ^ m * a₂ ^ (d - m) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h2k : 2 * k ≤ d := by omega
    rw [Finset.sum_Ico_eq_sum_range, show d - k + 1 - k = d - 2 * k + 1 by omega, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [show d - (k + i) = d - 2 * k - i + k by omega]
    ring
  have hswap : ∀ k m : ℕ,
      k ∈ Finset.range (d / 2 + 1) ∧ m ∈ Finset.Ico k (d - k + 1) ↔
        k ∈ Finset.range (min m (d - m) + 1) ∧ m ∈ Finset.range (d + 1) := by
    intro k m
    simp only [Finset.mem_range, Finset.mem_Ico, Nat.lt_add_one_iff, le_min_iff]
    omega
  rw [Finset.sum_congr rfl h1, Finset.sum_comm' hswap]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]

private theorem pairValues_sum_swap' (a₁ a₂ : ℂ) (d : ℕ) (c : ℕ → ℂ) :
    (∑ k ∈ Finset.range (d / 2 + 1),
        c k * (a₁ * a₂) ^ k * (∑ i ∈ Finset.range (d - 2 * k + 1), a₁ ^ i * a₂ ^ (d - 2 * k - i))) =
      ∑ m ∈ Finset.range (d + 1),
        (∑ k ∈ Finset.range (min m (d - m) + 1), c k) * a₁ ^ m * a₂ ^ (d - m) := by
  rw [← pairValues_sum_swap a₁ a₂ d c]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem coeffs_eq_zero_of_forall_ne_zero_eval (d : ℕ) (C : ℕ → ℂ)
    (h : ∀ x : ℂ, x ≠ 0 → ∑ m ∈ Finset.range (d + 1), C m * x ^ m = 0) :
    ∀ m : ℕ, m ≤ d → C m = 0 := by
  set p : Polynomial ℂ := ∑ m ∈ Finset.range (d + 1), Polynomial.C (C m) * Polynomial.X ^ m with hp
  have heval : ∀ x : ℂ, p.eval x = ∑ m ∈ Finset.range (d + 1), C m * x ^ m := by
    intro x
    simp [hp, Polynomial.eval_finsetSum]
  have hzero : p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot p ?_
    refine Set.Infinite.mono (s := ({0}ᶜ : Set ℂ)) ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    simpa [Polynomial.IsRoot, heval] using h x hx
  intro m hm
  have hcoeff : p.coeff m = C m := by
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    simp [Nat.lt_succ_of_le hm]
  rw [← hcoeff, hzero, Polynomial.coeff_zero]

end PairValuesIndependence

open PairValuesIndependence in

theorem solution
    (d : ℕ) (c : ℕ → ℂ)
    (h : ∀ a₁ a₂ : ℂ, a₁ * a₂ ≠ 0 →
      ∑ j ∈ Finset.range (d / 2 + 1),
        c j * (a₁ * a₂) ^ j * UnramifiedWhittaker.heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) (d - 2 * j) = 0) :
    ∀ j : ℕ, j ≤ d / 2 → c j = 0 := by

  have hmono : ∀ x : ℂ, x ≠ 0 →
      ∑ m ∈ Finset.range (d + 1), (∑ k ∈ Finset.range (min m (d - m) + 1), c k) * x ^ m = 0 := by
    intro x hx
    have hx1 : x * (1 : ℂ) ≠ 0 := by simpa using hx
    have h0 := h x 1 hx1
    simp only [pairValues_heckeRecursionSeq_one_eq_sum] at h0
    rw [pairValues_sum_swap' x 1 d c] at h0
    simpa only [one_pow, mul_one] using h0

  have hpartial := coeffs_eq_zero_of_forall_ne_zero_eval d _ hmono

  have hS : ∀ j : ℕ, j ≤ d / 2 → ∑ k ∈ Finset.range (j + 1), c k = 0 := by
    intro j hj
    have hjd : j ≤ d := le_trans hj (Nat.div_le_self d 2)
    have hmin : min j (d - j) = j := min_eq_left (by omega)
    have := hpartial j hjd
    rwa [hmin] at this
  intro j hj
  cases j with
  | zero => simpa using hS 0 (Nat.zero_le _)
  | succ i =>
    have h1 := hS (i + 1) hj
    have h2 := hS i (le_trans (Nat.le_succ i) hj)
    rw [Finset.sum_range_succ, h2, zero_add] at h1
    exact h1

end S_LanglandsTunnell_CubicInduction_eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero (solution)
