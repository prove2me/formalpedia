-- Prove2me | solution 1 for LevyStochCalc.Probability.norm_le_of_le_exitTime_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:43.67333+00:00
-- url     : https://prove2.me/submissions/e7b0ba3d-afef-44e4-ac71-ceae811ae6ea

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]
theorem LevyStochCalc.Probability.bddBelow_exitSet (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : BddBelow (exitSet X k ω) :=
  ⟨0, fun _ ht => ht.1⟩
/-- Up to and including the exit time, a continuous path started at a positive time has norm at
most `k`. The restriction to positive times is necessary: at time `0` the exit time is `0`
whenever the path already starts outside the ball. -/
theorem solution {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k s : ℝ}
    (hs : 0 < s) (hle : (s : WithTop ℝ) ≤ LevyStochCalc.Probability.exitTime X k ω) : ‖X ω s‖ ≤ k := by
  classical
  have hnot : ∀ u : ℝ, 0 ≤ u → u < s → ‖X ω u‖ ≤ k := by
    intro u hu0 hus
    by_contra hcon
    have hmem : u ∈ LevyStochCalc.Probability.exitSet X k ω := ⟨hu0, (not_le.mp hcon).le⟩
    have : LevyStochCalc.Probability.exitTime X k ω ≤ ((u : ℝ) : WithTop ℝ) := by
      rw [LevyStochCalc.Probability.exitTime, if_pos ⟨u, hmem⟩]
      exact_mod_cast csInf_le (LevyStochCalc.Probability.bddBelow_exitSet X k ω) hmem
    have hsu : ((s : ℝ) : WithTop ℝ) ≤ ((u : ℝ) : WithTop ℝ) := hle.trans this
    exact absurd (by exact_mod_cast hsu : s ≤ u) (not_le.mpr hus)
  have hlim : Filter.Tendsto (fun u => ‖X ω u‖) (nhdsWithin s (Set.Iio s)) (nhds ‖X ω s‖) :=
    (hX.norm.tendsto s).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u in nhdsWithin s (Set.Iio s), ‖X ω u‖ ≤ k := by
    have h0 : ∀ᶠ u in nhdsWithin s (Set.Iio s), 0 < u :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hs)
    filter_upwards [h0, self_mem_nhdsWithin] with u hu0 huc
    exact hnot u hu0.le huc
  exact le_of_tendsto hlim hev
