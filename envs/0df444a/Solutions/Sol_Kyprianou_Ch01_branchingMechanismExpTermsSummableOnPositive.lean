-- Prove2me | solution 1 for Kyprianou.Ch01.branchingMechanismExpTermsSummableOnPositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:35:02.637709+00:00
-- url     : https://prove2.me/submissions/9e006df6-744b-4d5e-9780-b7c6bd5ae674

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingMechanism_expUniformBound
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (offspring : PMF ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (z : ℝ) (hz : z ∈ Set.Icc a b) :
    Summable (fun k : ℕ => (offspring k).toReal *
      (1 - Real.exp (-z * ((k : ℝ) - 1)))) := by
  have hp : Summable (fun k : ℕ => (offspring k).toReal) :=
    ENNReal.summable_toReal offspring.tsum_coe_ne_top
  have hm : Summable (fun k : ℕ =>
      (1 + Real.exp b) * (offspring k).toReal) :=
    hp.mul_left _
  apply Summable.of_norm_bounded hm
  intro k
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (ENNReal.toReal_nonneg)]
  have hu := Kyprianou.Ch01.branchingMechanism_expUniformBound
    b (le_trans ha.le hab) k z (le_trans ha.le hz.1) hz.2
  have hbound := mul_le_mul_of_nonneg_left hu
    (show (0 : ℝ) ≤ (offspring k).toReal from ENNReal.toReal_nonneg)
  simpa only [mul_comm] using hbound
