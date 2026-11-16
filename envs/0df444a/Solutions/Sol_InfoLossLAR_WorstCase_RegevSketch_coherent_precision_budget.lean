-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.coherent_precision_budget
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:18:01.464263+00:00
-- url     : https://prove2.me/submissions/6a4fcbe4-f539-424d-b23d-8632ffcb60c7

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section

/-- A bit-length precision suffices to reserve half the inverse-budget
allowance for the accumulated coherent hybrid error. -/
theorem solution (steps budget : ℕ) (failure : ℕ → ℝ)
    (hfailure : ∀ i < steps,
      failure i ≤ (1 / (2 : ℝ) ^ (3 + Nat.size (steps+1) + Nat.size (budget+1))) ^ 2) :
    (∑ i ∈ Finset.range steps, 4 * Real.sqrt (failure i)) ≤
      1 / (2 * ((budget : ℝ)+1)) := by
  let k := 3 + Nat.size (steps+1) + Nat.size (budget+1)
  have hp : (0 : ℝ) < (2 : ℝ)^k := by positivity
  have hroot (i : ℕ) (hi : i < steps) :
      Real.sqrt (failure i) ≤ 1 / (2 : ℝ)^k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simpa [k] using hfailure i hi
  have hs : ((steps+1 : ℕ) : ℝ) ≤ (2 : ℝ)^Nat.size (steps+1) := by
    exact_mod_cast (Nat.lt_size_self (steps+1)).le
  have hb : ((budget+1 : ℕ) : ℝ) ≤ (2 : ℝ)^Nat.size (budget+1) := by
    exact_mod_cast (Nat.lt_size_self (budget+1)).le
  have hpow : (8 : ℝ) * ((steps : ℝ)+1) * ((budget : ℝ)+1) ≤ (2 : ℝ)^k := by
    dsimp [k]
    rw [pow_add, pow_add]
    norm_num only [show (2 : ℝ)^3 = 8 by norm_num]
    push_cast at hs hb
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (steps : ℝ)+1 by positivity)
      (sub_nonneg.mpr hb), mul_nonneg (show (0 : ℝ) ≤ (2 : ℝ)^Nat.size (budget+1) by positivity)
      (sub_nonneg.mpr hs)]
  have hsum : (∑ i ∈ Finset.range steps, 4 * Real.sqrt (failure i)) ≤
      (steps : ℝ) * (4 / (2 : ℝ)^k) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range steps, 4 * (1 / (2 : ℝ)^k) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hroot i (Finset.mem_range.mp hi)) (by norm_num)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  apply hsum.trans
  have hbudget : (0 : ℝ) < 2*((budget : ℝ)+1) := by positivity
  apply (le_div_iff₀ hbudget).mpr
  have hineq : ((steps : ℝ) * (4 / (2 : ℝ)^k)) * (2*((budget : ℝ)+1)) ≤ 1 := by
    have hbound : 8*(steps : ℝ)*((budget : ℝ)+1) ≤ (2 : ℝ)^k := by
      calc
        _ ≤ 8*((steps : ℝ)+1)*((budget : ℝ)+1) := by nlinarith [show (0 : ℝ) ≤ budget by positivity]
        _ ≤ _ := hpow
    have heq : ((steps : ℝ) * (4 / (2 : ℝ)^k)) * (2*((budget : ℝ)+1)) =
        (8*(steps : ℝ)*((budget : ℝ)+1))/(2 : ℝ)^k := by ring
    rw [heq]
    exact (div_le_one hp).2 hbound
  exact hineq

#print axioms solution
end
