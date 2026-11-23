-- Prove2me | solution 1 for Kyprianou.Ch01.pmfWeightedUnitIntervalBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:17:51.38568+00:00
-- url     : https://prove2.me/submissions/5a309bc8-d9d7-43dd-a2b5-37001e025eb6

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (p : PMF ℕ) (f : ℕ → ℝ)
    (hf : ∀ j : ℕ, 0 ≤ f j ∧ f j ≤ 1) :
    0 ≤ (∑' j : ℕ, (p j).toReal * f j) ∧
      (∑' j : ℕ, (p j).toReal * f j) ≤ 1 := by
  have hs : Summable (fun j : ℕ => (p j).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have htotal : (∑' j : ℕ, (p j).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun j => p.apply_ne_top j)]
    rw [p.tsum_coe]
    norm_num
  have hnonneg (j : ℕ) : 0 ≤ (p j).toReal * f j :=
    mul_nonneg ENNReal.toReal_nonneg (hf j).1
  have hle (j : ℕ) : (p j).toReal * f j ≤ (p j).toReal := by
    calc
      (p j).toReal * f j ≤ (p j).toReal * 1 :=
        mul_le_mul_of_nonneg_left (hf j).2 ENNReal.toReal_nonneg
      _ = (p j).toReal := mul_one _
  have hwsum : Summable (fun j : ℕ => (p j).toReal * f j) :=
    Summable.of_nonneg_of_le hnonneg hle hs
  constructor
  · exact tsum_nonneg hnonneg
  · calc
      (∑' j : ℕ, (p j).toReal * f j) ≤
          (∑' j : ℕ, (p j).toReal) :=
        Summable.tsum_le_tsum hle hwsum hs
      _ = 1 := htotal
