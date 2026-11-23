-- Prove2me | solution 1 for Kyprianou.Ch01.branchingMechanismExpSumCompactLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:29:42.389462+00:00
-- url     : https://prove2.me/submissions/41ad776e-6166-427d-9400-cc4cec874b92

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingMechanismExpTermsSummableOnPositive
import Theorems.Thm_Kyprianou_Ch01_branchingExpTermCompactLipschitz
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (offspring : PMF ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |(∑' k : ℕ, (offspring k).toReal *
       (1 - Real.exp (-y * ((k : ℝ) - 1)))) -
      (∑' k : ℕ, (offspring k).toReal *
       (1 - Real.exp (-x * ((k : ℝ) - 1))))| ≤
    (a⁻¹ + Real.exp b) * |y - x| := by
  let L : ℝ := a⁻¹ + Real.exp b
  have hp : Summable (fun k : ℕ => (offspring k).toReal) :=
    ENNReal.summable_toReal offspring.tsum_coe_ne_top
  have hpmass : (∑' k : ℕ, (offspring k).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq
      (fun k : ℕ => offspring.apply_ne_top k)]
    simp
  have hs (z : ℝ) (hz : z ∈ Set.Icc a b) :=
    Kyprianou.Ch01.branchingMechanismExpTermsSummableOnPositive
      offspring a b ha hab z hz
  have hbd (k : ℕ) :
      ‖(offspring k).toReal *
        ((1 - Real.exp (-y * ((k : ℝ) - 1))) -
         (1 - Real.exp (-x * ((k : ℝ) - 1))))‖ ≤
       (L * |y - x|) * (offspring k).toReal := by
    have he := Kyprianou.Ch01.branchingExpTermCompactLipschitz
      a b ha hab k x y hx hy
    have hs := mul_le_mul_of_nonneg_left he
      (ENNReal.toReal_nonneg : 0 ≤ (offspring k).toReal)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (ENNReal.toReal_nonneg : 0 ≤ (offspring k).toReal)]
    have heq :
        |(1 - Real.exp (-y * ((k : ℝ) - 1))) -
         (1 - Real.exp (-x * ((k : ℝ) - 1)))| =
        |Real.exp (-y * ((k : ℝ) - 1)) -
         Real.exp (-x * ((k : ℝ) - 1))| := by
      rw [show (1 - Real.exp (-y * ((k : ℝ) - 1))) -
        (1 - Real.exp (-x * ((k : ℝ) - 1))) =
        -(Real.exp (-y * ((k : ℝ) - 1)) -
          Real.exp (-x * ((k : ℝ) - 1))) by ring, abs_neg]
    rw [heq]
    simpa [L, mul_comm, mul_left_comm, mul_assoc] using hs
  have hbound :=
    tsum_of_norm_bounded
      (hp.mul_left (L * |y - x|)).hasSum hbd
  rw [tsum_mul_left, hpmass, mul_one] at hbound
  have hdiff :
      (∑' k : ℕ, (offspring k).toReal *
        ((1 - Real.exp (-y * ((k : ℝ) - 1))) -
         (1 - Real.exp (-x * ((k : ℝ) - 1))))) =
      (∑' k : ℕ, (offspring k).toReal *
        (1 - Real.exp (-y * ((k : ℝ) - 1)))) -
      (∑' k : ℕ, (offspring k).toReal *
        (1 - Real.exp (-x * ((k : ℝ) - 1)))) := by
    simpa only [mul_sub] using (hs y hy).tsum_sub (hs x hx)
  rw [← hdiff, ← Real.norm_eq_abs]
  simpa only [L] using hbound
