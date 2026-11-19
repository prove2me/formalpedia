-- Prove2me | solution 1 for Kyprianou.Ch01.branchingDiscountedOffspringSummable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:43:16.70021+00:00
-- url     : https://prove2.me/submissions/3bcc15d2-2100-4564-9b36-3abfe43af17a

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

/-- The discounted offspring PMF is real summable and has unit mass. -/
theorem solution (offspring : PMF ℕ) (q : ℝ) (hq : 0 < q) :
    (∑' k : ℕ, (offspring k).toReal) = 1 ∧
    Summable (fun k : ℕ =>
      (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
  have hfinite (k : ℕ) : offspring k ≠ ∞ :=
    offspring.apply_ne_top k
  have hpsum : Summable (fun k : ℕ => (offspring k).toReal) :=
    ENNReal.summable_toReal offspring.tsum_coe_ne_top
  have hpnorm : (∑' k : ℕ, (offspring k).toReal) = 1 := by
    calc
      (∑' k : ℕ, (offspring k).toReal) =
          (∑' k : ℕ, offspring k).toReal :=
            (ENNReal.tsum_toReal_eq hfinite).symm
      _ = 1 := by simp
  refine ⟨hpnorm, ?_⟩
  have hle (k : ℕ) : Real.exp (-q * (k : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith [mul_nonneg hq.le hk]
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _)
  · intro k
    calc
      (offspring k).toReal * Real.exp (-q * (k : ℝ)) ≤
        (offspring k).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hle k) ENNReal.toReal_nonneg
      _ = (offspring k).toReal := mul_one _
  · exact hpsum
