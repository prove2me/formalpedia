-- Prove2me | solution 1 for LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:39.03533+00:00
-- url     : https://prove2.me/submissions/6ccfafa5-bf80-45b0-86d2-dbdace112195

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
import Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_readable
import Theorems.Thm_LevyStochCalc_Probability_tendsto_dyadicTime_dyadicIndex_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
theorem LevyStochCalc.Probability.dyadicTime_nonneg {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) : 0 ≤ dyadicTime T n k :=
  le_min (by positivity) hT
theorem LevyStochCalc.Probability.dyadicTime_le {T : ℝ} (n k : ℕ) : dyadicTime T n k ≤ T := min_le_right _ _
theorem LevyStochCalc.Probability.dyadicTime_mem_Icc {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) :
    dyadicTime T n k ∈ Set.Icc (0 : ℝ) T :=
  ⟨dyadicTime_nonneg hT n k, dyadicTime_le n k⟩
variable {M : ℝ → Ω → ℝ} {T : ℝ}
theorem LevyStochCalc.Probability.dyadicIndex_le {T t : ℝ} (hT : 0 < T) (ht : t ≤ T) (n : ℕ) :
    dyadicIndex T t n ≤ 2 ^ n := by
  refine Nat.ceil_le.mpr ?_
  rw [div_le_iff₀ hT]
  push_cast
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
/-- **Right-continuity identifies the supremum over the window with the supremum of the sampled
running maxima.** -/
theorem solution (hT : 0 ≤ T) {ω : Ω}
    (hcad : ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞))
      = ⨆ n, (‖LevyStochCalc.Probability.dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun n => ?_)
  · rcases eq_or_lt_of_le hT with hT0 | hTpos
    · have ht0 : (t : ℝ) = 0 := le_antisymm (hT0 ▸ t.2.2) t.2.1
      refine le_iSup_of_le 0 ?_
      rw [LevyStochCalc.Probability.enorm_dyadicRunMax_readable]
      refine le_iSup_of_le ⟨0, Nat.succ_pos _⟩ (le_of_eq ?_)
      have hd0 : LevyStochCalc.Probability.dyadicTime T 0 0 = 0 := by
        simp [LevyStochCalc.Probability.dyadicTime, ← hT0]
      rw [hd0, ht0]
    · have hbd : ∀ n : ℕ, (‖M (LevyStochCalc.Probability.dyadicTime T n (LevyStochCalc.Probability.dyadicIndex T (t : ℝ) n)) ω‖₊ : ℝ≥0∞)
          ≤ ⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞) := by
        intro n
        refine le_iSup_of_le n ?_
        rw [LevyStochCalc.Probability.enorm_dyadicRunMax_readable]
        exact le_iSup_of_le
          ⟨LevyStochCalc.Probability.dyadicIndex T (t : ℝ) n, Nat.lt_succ_of_le (LevyStochCalc.Probability.dyadicIndex_le hTpos t.2.2 n)⟩ le_rfl
      have hMs : Filter.Tendsto
          (fun n => M (LevyStochCalc.Probability.dyadicTime T n (LevyStochCalc.Probability.dyadicIndex T (t : ℝ) n)) ω) Filter.atTop
          (nhds (M (t : ℝ) ω)) :=
        (LevyStochCalc.Probability.tendsto_nhdsGE_of_nhdsGT (hcad (t : ℝ))).comp
          (LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex_readable hTpos t.2.1 t.2.2)
      have hconv : Filter.Tendsto
          (fun n => (‖M (LevyStochCalc.Probability.dyadicTime T n (LevyStochCalc.Probability.dyadicIndex T (t : ℝ) n)) ω‖₊ : ℝ≥0∞))
          Filter.atTop (nhds ((‖M (t : ℝ) ω‖₊ : ℝ≥0∞))) :=
        (ENNReal.continuous_coe.tendsto _).comp hMs.nnnorm
      exact le_of_tendsto hconv (Filter.Eventually.of_forall hbd)
  · rw [LevyStochCalc.Probability.enorm_dyadicRunMax_readable]
    exact iSup_le fun k =>
      le_iSup_of_le ⟨LevyStochCalc.Probability.dyadicTime T n (k : ℕ), LevyStochCalc.Probability.dyadicTime_mem_Icc hT n (k : ℕ)⟩ le_rfl
