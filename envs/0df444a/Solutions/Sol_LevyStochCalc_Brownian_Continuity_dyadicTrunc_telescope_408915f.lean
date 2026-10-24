-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dyadicTrunc_telescope_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:37:06.994885+00:00
-- url     : https://prove2.me/submissions/ed300f43-1dec-445a-8160-72405db207a0

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
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_succ_step_408915f

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
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc.Brownian.Continuity in
/-- **Telescoping bound across levels.** For `x ∈ [0,1]` and `m ≤ L`, the
truncation increment from level `m` to level `L` is bounded by the sum of the
per-level bounds `b (m+1) + ⋯ + b L`. -/
lemma solution {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ} (hm : N ≤ m + 1) :
    ∀ L, m ≤ L → |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc L x) - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m x)|
      ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
    rw [sub_self, abs_zero, Finset.Ico_self, Finset.sum_empty]
  | succ L hmL ih =>
    calc |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc (L + 1) x) - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m x)|
        ≤ |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc (L + 1) x) - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc L x)|
          + |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc L x) - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m x)| := abs_sub_le _ _ _
      _ ≤ b (L + 1) + ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
          refine add_le_add ?_ ih
          exact LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step_408915f hb hf (by omega) hx0 hx1
      _ = ∑ n ∈ Finset.Ico (m + 1) (L + 2), b n := by
          rw [Finset.sum_Ico_succ_top (by omega : m + 1 ≤ L + 1)]
          ring
