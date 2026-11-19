-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorWeightedQuotientTendstoNoNull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T11:28:30.880376+00:00
-- url     : https://prove2.me/submissions/ab4f69a3-3f0a-416a-97db-be9fe10016c9

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_Kyprianou_Ch01_branchingOffDiagonalQuotientConvergence
import Theorems.Thm_Kyprianou_Ch01_nonnegativeSeriesWeightedMassTendsto
import Theorems.Thm_Kyprianou_Ch01_branchingOffDiagonalQuotientSummablePositive
import Theorems.Thm_Kyprianou_Ch01_branchingDiscountedOffspringSummable
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

/-- The no-null-jumps source condition prevents hidden first-order exit mass. -/
theorem solution
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (q : ℝ) (hq : 0 < q) :
    Tendsto (fun t : ℝ =>
      ∑' k : ℕ,
        ((if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t) *
          Real.exp (-q * (k : ℝ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 ((rate : ℝ) * ∑' k : ℕ,
        (offspring k).toReal * Real.exp (-q * (k : ℝ)))) := by
  let a : ℝ → ℕ → ℝ := fun t k =>
    (if k = 1 then (0 : ℝ)
      else ((law 1 (Real.toNNReal t)) k).toReal) / t
  let b : ℕ → ℝ := fun k =>
    if k = 1 then 0 else (rate : ℝ) * (offspring k).toReal
  let w : ℕ → ℝ := fun k => Real.exp (-q * (k : ℝ))
  have hqconv := Kyprianou.Ch01.branchingOffDiagonalQuotientConvergence
    law rate offspring hinit hRates
  have heq (k : ℕ) : b k = (rate : ℝ) * (offspring k).toReal := by
    dsimp [b]
    by_cases hk : k = 1
    · subst k
      simp [hNoNullJumps]
    · simp [hk]
  have hp : Summable (fun k : ℕ => (offspring k).toReal) :=
    ENNReal.summable_toReal offspring.tsum_coe_ne_top
  have hbs : Summable b := by
    have hbfun : b = fun k => (rate : ℝ) * (offspring k).toReal :=
      funext heq
    rw [hbfun]
    exact hp.mul_left (rate : ℝ)
  have hbsum : (∑' k, b k) = (rate : ℝ) := by
    simp_rw [heq]
    rw [hp.tsum_mul_left,
      (Kyprianou.Ch01.branchingDiscountedOffspringSummable offspring q hq).1]
    ring
  have ha : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ k, 0 ≤ a t k := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (Kyprianou.Ch01.branchingOffDiagonalQuotientSummablePositive law t ht).1
  have hasum : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), Summable (a t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (Kyprianou.Ch01.branchingOffDiagonalQuotientSummablePositive law t ht).2
  have hb : ∀ k, 0 ≤ b k := by
    intro k
    rw [heq]
    exact mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  have hw (k : ℕ) : 0 ≤ w k ∧ w k ≤ 1 := by
    constructor
    · exact (Real.exp_pos _).le
    · dsimp [w]
      rw [Real.exp_le_one_iff]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [mul_nonneg hq.le hk]
  have hpoint (k : ℕ) :
      Tendsto (fun t => a t k) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (b k)) := by
    exact hqconv.1 k
  have hmass : Tendsto (fun t => ∑' k, a t k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (∑' k, b k)) := by
    simpa only [hbsum] using hqconv.2
  have hweighted := Kyprianou.Ch01.nonnegativeSeriesWeightedMassTendsto
    a b w ha hasum hb hbs hw hpoint hmass
  have hWvalue : (∑' k, b k * w k) =
      (rate : ℝ) * ∑' k : ℕ,
        (offspring k).toReal * Real.exp (-q * (k : ℝ)) := by
    simp_rw [heq, w, mul_assoc]
    exact
      (Kyprianou.Ch01.branchingDiscountedOffspringSummable
        offspring q hq).2.tsum_mul_left (rate : ℝ)
  change Tendsto (fun t => ∑' k, a t k * w k)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (𝓝 ((rate : ℝ) * ∑' k : ℕ,
      (offspring k).toReal * Real.exp (-q * (k : ℝ))))
  rw [← hWvalue]
  exact hweighted
