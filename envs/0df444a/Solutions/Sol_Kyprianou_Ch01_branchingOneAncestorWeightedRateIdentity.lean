-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorWeightedRateIdentity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:04:42.901746+00:00
-- url     : https://prove2.me/submissions/5c9044f7-67b5-4bc5-a3b9-03150c4a68a3

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace WRIAux
theorem mom
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
end WRIAux

theorem solution
    (rate : ℝ≥0) (offspring : PMF ℕ)
    (hNoNullJumps : offspring 1 = 0)
    (q : ℝ) (hq : 0 < q) :
    (∑' k : ℕ,
      (if k = 1 then -(rate : ℝ)
       else (rate : ℝ) * (offspring k).toReal) *
      Real.exp (-q * (k : ℝ))) =
      -(branchingMechanism (rate : ℝ) offspring q) *
        Real.exp (-q) := by
  have hs : Summable (fun k => (offspring k).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have hs2 : Summable (fun k : ℕ => (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
    have : Real.exp (-q * (k : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ k := k.cast_nonneg; nlinarith
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg this
  have heq : ∀ k : ℕ, (if k = 1 then -(rate : ℝ) else (rate : ℝ) * (offspring k).toReal) *
      Real.exp (-q * (k : ℝ)) =
      (rate : ℝ) * ((offspring k).toReal * Real.exp (-q * (k : ℝ))) +
        (if k = 1 then -(rate : ℝ) * Real.exp (-q) else 0) := by
    intro k
    by_cases hk : k = 1
    · subst hk; simp [hNoNullJumps]
    · simp [hk]; ring
  simp_rw [heq]
  rw [(hs2.mul_left _).tsum_add (summable_of_ne_finset_zero (s := {1}) (by
      intro k hk; simp at hk; simp [hk])), tsum_mul_left, tsum_ite_eq]
  unfold branchingMechanism
  rw [WRIAux.mom offspring q hq]
  have : Real.exp q * Real.exp (-q) = 1 := by rw [← Real.exp_add]; simp
  linear_combination -(rate : ℝ) * (∑' k : ℕ, (offspring k).toReal * Real.exp (-q * (k : ℝ))) * this
