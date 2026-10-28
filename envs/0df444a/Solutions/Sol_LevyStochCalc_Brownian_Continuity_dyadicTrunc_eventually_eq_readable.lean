-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:56.168212+00:00
-- url     : https://prove2.me/submissions/6d9ee61a-e64c-4a88-9a47-55898078b7a2

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
/-- A dyadic rational coincides with its own level-`L` truncation for all
sufficiently large `L`. -/
lemma solution {s : ℝ} (hs : s ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → LevyStochCalc.Brownian.Continuity.dyadicTrunc L s = s := by
  obtain ⟨k, n, hkn⟩ := hs
  refine ⟨n, fun L hL => ?_⟩
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - n) * (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hL]
  have hsL : s * 2 ^ L = ((k * 2 ^ (L - n) : ℤ) : ℝ) := by
    rw [hkn, zpow_neg, zpow_natCast, hpow]
    push_cast
    field_simp
  rw [LevyStochCalc.Brownian.Continuity.dyadicTrunc, hsL, Int.floor_intCast, hkn, zpow_neg, zpow_natCast, hpow]
  push_cast
  field_simp
