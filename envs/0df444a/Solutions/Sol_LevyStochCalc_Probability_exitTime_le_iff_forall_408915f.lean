-- Prove2me | solution 1 for LevyStochCalc.Probability.exitTime_le_iff_forall_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:08:27.619986+00:00
-- url     : https://prove2.me/submissions/15ec4fd4-f2e0-461a-9706-abd8c6a43322

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ExitTime
import Mathlib.Data.Rat.Denumerable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone
import Theorems.Thm_LevyStochCalc_Probability_abs_clamp_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_408915f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]
theorem LevyStochCalc.Probability.gridPt_mem_Icc {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : gridPt t n ∈ Set.Icc (0 : ℝ) t :=
  ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
theorem LevyStochCalc.Probability.exists_gridPt_near {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) {δ : ℝ}
    (hδ : 0 < δ) : ∃ n : ℕ, |gridPt t n - s| < δ := by
  obtain ⟨q, hq⟩ := exists_rat_near s hδ
  refine ⟨Denumerable.eqv ℚ q, ?_⟩
  have hqn : ((Denumerable.eqv ℚ).symm (Denumerable.eqv ℚ q) : ℚ) = q := Equiv.symm_apply_apply _ _
  rw [gridPt, hqn]
  refine lt_of_le_of_lt (abs_clamp_sub_le_408915f ht hs _) ?_
  rwa [abs_sub_comm]
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
/-- The comparison `exitTime X k ω ≤ t` is decided by the values of a continuous path on the
rationals of `[0, t]`. -/
theorem solution {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    LevyStochCalc.Probability.exitTime X k ω ≤ (t : WithTop ℝ) ↔
      ∀ n : ℕ, ∃ m : ℕ, k - ((n : ℝ) + 1)⁻¹ < ‖X ω (LevyStochCalc.Probability.gridPt t m)‖ := by
  rw [LevyStochCalc.Probability.exitTime_le_iff_408915f hX]
  constructor
  · rintro ⟨s, hs, hks⟩ n
    have hε : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hca : ContinuousAt (fun r => ‖X ω r‖) s := hX.norm.continuousAt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hca _ hε
    obtain ⟨m, hm⟩ := LevyStochCalc.Probability.exists_gridPt_near ht hs hδ
    refine ⟨m, ?_⟩
    have hdist : dist (LevyStochCalc.Probability.gridPt t m) s < δ := by rwa [Real.dist_eq]
    have hclose := hδ' hdist
    rw [Real.dist_eq] at hclose
    have hle : ‖X ω s‖ - ‖X ω (LevyStochCalc.Probability.gridPt t m)‖ ≤ |‖X ω (LevyStochCalc.Probability.gridPt t m)‖ - ‖X ω s‖| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · intro hall
    obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_isMaxOn
      (Set.nonempty_Icc.2 ht) hX.norm.continuousOn
    refine ⟨s₀, hs₀, ?_⟩
    rcases lt_or_ge ‖X ω s₀‖ k with hlt | hge
    · exfalso
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < k - ‖X ω s₀‖ by linarith)
      obtain ⟨m, hm⟩ := hall n
      have hle : ‖X ω (LevyStochCalc.Probability.gridPt t m)‖ ≤ ‖X ω s₀‖ := hmax (LevyStochCalc.Probability.gridPt_mem_Icc ht m)
      rw [one_div] at hn
      linarith
    · exact hge
