-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignment_row_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:32.865172+00:00
-- url     : https://prove2.me/submissions/70d6da2d-37aa-422a-8a07-fe78abf5efc6

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α]
    (size : α → ℕ) {k : ℕ} (hk : 1 ≤ k) (σ : α → Option (Fin k))
    {z D : ℝ} (hz : 1 < z) (hsize : ∀ p, z ≤ (size p : ℝ))
    (hcut : (assignmentProduct size σ : ℝ) ≤ D) :
    (∏ p, localRow (size p) k (σ p)) ≤
      Real.exp ((k : ℝ) * Real.log D / ((z - 1) * Real.log z)) := by
  classical
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hz1 : 0 < z - 1 := sub_pos.mpr hz
  have hk1 : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hk)
  have hpos (p : α) : 0 < (size p : ℝ) := hz0.trans_le (hsize p)
  have hlog : ((assignmentSupport σ).card : ℝ) * Real.log z ≤ Real.log D := by
    calc
      _ = ∑ p ∈ assignmentSupport σ, Real.log z := by simp
      _ ≤ ∑ p ∈ assignmentSupport σ, Real.log (size p) :=
        Finset.sum_le_sum fun p _ => Real.log_le_log hz0 (hsize p)
      _ = Real.log (assignmentProduct size σ) := by
        rw [assignmentProduct, Nat.cast_prod, Real.log_prod (fun p _ => (hpos p).ne')]
      _ ≤ Real.log D := Real.log_le_log (by
        rw [assignmentProduct, Nat.cast_prod]
        exact Finset.prod_pos fun p _ => hpos p) hcut
  calc
    (∏ p, localRow (size p) k (σ p)) =
        ∏ p ∈ assignmentSupport σ, (1 + ((k : ℝ) - 1) / ((size p : ℝ) - 1)) := by
      simp only [assignmentSupport, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p _
      cases σ p <;> simp [localRow]
    _ ≤ ∏ _ ∈ assignmentSupport σ, Real.exp ((k : ℝ) / (z - 1)) := by
      apply Finset.prod_le_prod
      · intro p _
        exact add_nonneg zero_le_one
          (div_nonneg hk1 (hz1.le.trans (sub_le_sub_right (hsize p) 1)))
      · intro p _
        calc
          _ ≤ 1 + (k : ℝ) / (z - 1) := add_le_add (le_refl 1)
            (div_le_div₀ (Nat.cast_nonneg k) (sub_le_self _ zero_le_one) hz1
              (sub_le_sub_right (hsize p) 1))
          _ ≤ Real.exp ((k : ℝ) / (z - 1)) := by
            simpa [add_comm] using Real.add_one_le_exp ((k : ℝ) / (z - 1))
    _ = Real.exp (((assignmentSupport σ).card : ℝ) * ((k : ℝ) / (z - 1))) := by
      simp [Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hcount := (le_div_iff₀ (Real.log_pos hz)).mpr hlog
      have hbound := mul_le_mul_of_nonneg_right hcount
        (div_nonneg (Nat.cast_nonneg k) hz1.le)
      calc
        _ ≤ Real.log D / Real.log z * ((k : ℝ) / (z - 1)) := hbound
        _ = _ := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
end LongGapsBetweenPrimes
