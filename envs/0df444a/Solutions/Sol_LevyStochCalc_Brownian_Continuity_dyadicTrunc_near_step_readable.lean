-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dyadicTrunc_near_step_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:57.209251+00:00
-- url     : https://prove2.me/submissions/d1d5e7d1-3152-4719-a7b9-d8f2dfb260ba

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
/-- **Cross-point step at a fixed level.** For `0 ≤ s ≤ t ≤ 1` with
`t − s ≤ 2^{-m}`, the level-`m` truncations of `s` and `t` are equal or adjacent
level-`m` dyadics, so `|f(trunc_m s) − f(trunc_m t)| ≤ b m`. -/
lemma solution {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {m : ℕ} (hm : N ≤ m) {s t : ℝ} (hs0 : 0 ≤ s) (ht1 : t ≤ 1) (hst : s ≤ t)
    (hclose : t - s ≤ (1 / 2) ^ m) :
    |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m s) - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m t)| ≤ b m := by
  set ks : ℤ := ⌊s * 2 ^ m⌋ with hks
  set kt : ℤ := ⌊t * 2 ^ m⌋ with hkt
  have hks0 : 0 ≤ ks := by rw [hks]; apply Int.floor_nonneg.mpr; positivity
  have hmono : ks ≤ kt := by
    rw [hks, hkt]; apply Int.floor_le_floor
    exact mul_le_mul_of_nonneg_right hst (by positivity)
  have hclose' : t * 2 ^ m ≤ s * 2 ^ m + 1 := by
    have hmul : (t - s) * 2 ^ m ≤ 1 := by
      calc (t - s) * 2 ^ m ≤ (1 / 2) ^ m * 2 ^ m :=
            mul_le_mul_of_nonneg_right hclose (by positivity)
        _ = 1 := by rw [div_pow, one_pow, div_mul_cancel₀]; positivity
    nlinarith
  have hkt_le : kt ≤ ks + 1 := by
    rw [hkt, hks]
    calc ⌊t * 2 ^ m⌋ ≤ ⌊s * 2 ^ m + 1⌋ := Int.floor_le_floor (by linarith)
      _ = ⌊s * 2 ^ m⌋ + 1 := Int.floor_add_one _
  have hTs : LevyStochCalc.Brownian.Continuity.dyadicTrunc m s = ((ks : ℤ) : ℝ) / 2 ^ m := by rw [LevyStochCalc.Brownian.Continuity.dyadicTrunc, ← hks]
  have hTt : LevyStochCalc.Brownian.Continuity.dyadicTrunc m t = ((kt : ℤ) : ℝ) / 2 ^ m := by rw [LevyStochCalc.Brownian.Continuity.dyadicTrunc, ← hkt]
  rcases (by omega : kt = ks ∨ kt = ks + 1) with he | he
  · rw [hTs, hTt, he, sub_self, abs_zero]; exact hb m
  · have hbnd : ks + 1 ≤ (2 : ℤ) ^ m := by
      have hktle : (kt : ℝ) ≤ t * 2 ^ m := Int.floor_le _
      have hkt_le2 : (kt : ℝ) ≤ (2 : ℝ) ^ m :=
        le_trans hktle (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) m])
      have : (kt : ℤ) ≤ (2 : ℤ) ^ m := by exact_mod_cast hkt_le2
      omega
    have hap := hf m hm ks hks0 hbnd
    rw [hTs, hTt, he, abs_sub_comm]
    exact_mod_cast hap
