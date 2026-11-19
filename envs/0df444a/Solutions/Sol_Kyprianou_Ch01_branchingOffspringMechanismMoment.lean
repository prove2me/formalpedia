-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOffspringMechanismMoment
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:04:41.97837+00:00
-- url     : https://prove2.me/submissions/345af76e-7dfe-4a10-953a-7f5ab688515d

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open MeasureTheory
set_option autoImplicit false

theorem solution
    (offspring : PMF ℕ) (q : ℝ) (hq : 0 < q) :
    (∑' k : ℕ,
      (offspring k).toReal *
        (1 - Real.exp (-q * ((k : ℝ) - 1)))) =
      1 - Real.exp q *
        (∑' k : ℕ,
          (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
  have hs : Summable (fun k => (offspring k).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have h1 : ∑' k, (offspring k).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun k => PMF.apply_ne_top offspring k), PMF.tsum_coe]; simp
  have hs2 : Summable (fun k : ℕ => (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
    have : Real.exp (-q * (k : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg this
  have heq : ∀ k : ℕ, (offspring k).toReal * (1 - Real.exp (-q * ((k : ℝ) - 1))) =
      (offspring k).toReal - Real.exp q * ((offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
    intro k
    have : Real.exp (-q * ((k : ℝ) - 1)) = Real.exp q * Real.exp (-q * (k : ℝ)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  simp_rw [heq]
  rw [hs.tsum_sub (hs2.mul_left _), tsum_mul_left, h1]
