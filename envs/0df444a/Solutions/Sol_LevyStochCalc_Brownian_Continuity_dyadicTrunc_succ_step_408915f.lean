-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:35:56.477409+00:00
-- url     : https://prove2.me/submissions/3d030d59-27f3-4adf-80bd-40c581c0ad49

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Continuity
/-- `2⌊y⌋ ≤ ⌊2y⌋ ≤ 2⌊y⌋ + 1`. -/
lemma LevyStochCalc.Brownian.Continuity.floor_two_mul_bounds (y : ℝ) :
    2 * ⌊y⌋ ≤ ⌊2 * y⌋ ∧ ⌊2 * y⌋ ≤ 2 * ⌊y⌋ + 1 := by
  refine ⟨?_, ?_⟩
  · apply Int.le_floor.mpr
    push_cast
    linarith [Int.floor_le y]
  · have h2 : ⌊2 * y⌋ < 2 * ⌊y⌋ + 2 := by
      apply Int.floor_lt.mpr
      push_cast
      linarith [Int.lt_floor_add_one y]
    omega
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc.Brownian.Continuity in
/-- **Single refinement step.** For `x ∈ [0,1]`, the level-`(n+1)` truncation
differs from the level-`n` truncation by at most one consecutive level-`(n+1)`
dyadic increment, hence `|f(trunc_{n+1} x) − f(trunc_n x)| ≤ b (n+1)`. -/
lemma solution {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {n : ℕ} (hn : N ≤ n + 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc (n + 1) x) - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc n x)| ≤ b (n + 1) := by
  set k : ℤ := ⌊x * 2 ^ n⌋ with hk
  set j : ℤ := ⌊x * 2 ^ (n + 1)⌋ with hj
  have hjk : j = ⌊2 * (x * 2 ^ n)⌋ := by rw [hj]; congr 1; rw [pow_succ]; ring
  obtain ⟨hlo, hhi⟩ := LevyStochCalc.Brownian.Continuity.floor_two_mul_bounds (x * 2 ^ n)
  rw [← hjk] at hlo hhi
  have hk0 : 0 ≤ k := by
    rw [hk]; apply Int.floor_nonneg.mpr; positivity
  -- Truncations expressed over the common denominator `2^(n+1)`.
  have hDn : LevyStochCalc.Brownian.Continuity.dyadicTrunc n x = ((2 * k : ℤ) : ℝ) / 2 ^ (n + 1) := by
    rw [LevyStochCalc.Brownian.Continuity.dyadicTrunc, ← hk, pow_succ]; push_cast; ring
  have hDn1 : LevyStochCalc.Brownian.Continuity.dyadicTrunc (n + 1) x = ((j : ℤ) : ℝ) / 2 ^ (n + 1) := by
    rw [LevyStochCalc.Brownian.Continuity.dyadicTrunc, ← hj]
  rcases (by omega : j = 2 * k ∨ j = 2 * k + 1) with hjeq | hjeq
  · -- No refinement: the two truncations coincide.
    rw [hDn1, hDn, hjeq, sub_self, abs_zero]
    exact hb (n + 1)
  · -- One refinement step `(2k) → (2k+1)` at level `n+1`.
    have hbound : 2 * k + 1 ≤ (2 : ℤ) ^ (n + 1) := by
      have hjle : (j : ℝ) ≤ x * 2 ^ (n + 1) := Int.floor_le _
      have hj_le : (j : ℝ) ≤ (2 : ℝ) ^ (n + 1) :=
        le_trans hjle (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (n + 1)])
      have : (j : ℤ) ≤ (2 : ℤ) ^ (n + 1) := by exact_mod_cast hj_le
      omega
    have hap := hf (n + 1) hn (2 * k) (by omega) hbound
    rw [hDn1, hDn, hjeq]
    exact_mod_cast hap
