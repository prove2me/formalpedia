-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dyadicTrunc_telescope_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:00.025365+00:00
-- url     : https://prove2.me/submissions/e3a56642-bb5f-4e31-955c-f15f5e89d8e7

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_succ_step_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
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
          exact LevyStochCalc.Brownian.Continuity.dyadicTrunc_succ_step_readable hb hf (by omega) hx0 hx1
      _ = ∑ n ∈ Finset.Ico (m + 1) (L + 2), b n := by
          rw [Finset.sum_Ico_succ_top (by omega : m + 1 ≤ L + 1)]
          ring
