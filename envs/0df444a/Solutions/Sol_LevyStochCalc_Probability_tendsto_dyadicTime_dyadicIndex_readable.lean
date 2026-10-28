-- Prove2me | solution 1 for LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:50.79664+00:00
-- url     : https://prove2.me/submissions/88382a09-2ff4-4b16-af55-d2ab2d2d6145

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}
theorem LevyStochCalc.Probability.le_dyadicTime_dyadicIndex {T t : ℝ} (hT : 0 < T) (htT : t ≤ T) (n : ℕ) :
    t ≤ dyadicTime T n (dyadicIndex T t n) := by
  have hpow : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hceil : t * 2 ^ n / T ≤ (dyadicIndex T t n : ℝ) := Nat.le_ceil _
  have h1 : t * 2 ^ n ≤ (dyadicIndex T t n : ℝ) * T := (div_le_iff₀ hT).mp hceil
  have hmul : t ≤ (dyadicIndex T t n : ℝ) * T / 2 ^ n := (le_div_iff₀ hpow).mpr h1
  exact le_min hmul htT
theorem LevyStochCalc.Probability.dyadicTime_dyadicIndex_le_add {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (n : ℕ) :
    dyadicTime T n (dyadicIndex T t n) ≤ t + T / 2 ^ n := by
  have hpow : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlt : (dyadicIndex T t n : ℝ) < t * 2 ^ n / T + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  refine le_trans (min_le_left _ _) ?_
  rw [div_le_iff₀ hpow]
  have hexp : (t + T / 2 ^ n) * 2 ^ n = t * 2 ^ n + T := by field_simp
  rw [hexp]
  have : (dyadicIndex T t n : ℝ) * T ≤ (t * 2 ^ n / T + 1) * T :=
    mul_le_mul_of_nonneg_right hlt.le hT.le
  calc (dyadicIndex T t n : ℝ) * T ≤ (t * 2 ^ n / T + 1) * T := this
    _ = t * 2 ^ n + T := by field_simp
/-- The dyadic points chosen by `dyadicIndex` approach `t` from the right. -/
theorem solution {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    Filter.Tendsto (fun n => LevyStochCalc.Probability.dyadicTime T n (LevyStochCalc.Probability.dyadicIndex T t n)) Filter.atTop
      (nhdsWithin t (Set.Ici t)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Filter.Eventually.of_forall fun n => LevyStochCalc.Probability.le_dyadicTime_dyadicIndex hT htT n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => t) (h := fun n => t + T / 2 ^ n) tendsto_const_nhds ?_
    (fun n => LevyStochCalc.Probability.le_dyadicTime_dyadicIndex hT htT n)
    (fun n => LevyStochCalc.Probability.dyadicTime_dyadicIndex_le_add hT ht n)
  have hhalf : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hd : ∀ n : ℕ, T / 2 ^ n = T * ((1 : ℝ) / 2) ^ n := fun n => by
    rw [div_pow, one_pow]
    ring
  have htend0 : Filter.Tendsto (fun n : ℕ => T / 2 ^ n) Filter.atTop (nhds 0) := by
    simp only [hd]
    simpa using hhalf.const_mul T
  simpa using tendsto_const_nhds.add htend0
