-- Prove2me | solution 1 for Kyprianou.Ch02.locallyAbsSummableCumulativeJumpSeriesRightContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:27:30.939361+00:00
-- url     : https://prove2.me/submissions/0a825841-363f-464e-af80-b5eee28dec8b

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_truncatedCumulativeAtomicSeriesAgreementV1
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Local cumulative jump-series regularity. -/
theorem solution
    (g : ℝ≥0 → ℝ)
    (hs : ∀ T : ℝ≥0, Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|))
    (t : ℝ≥0) :
    ContinuousWithinAt (fun u : ℝ≥0 =>
      ∑' s : Set.Ioc (0 : ℝ≥0) u, g s) (Ici t) t := by
  classical
  let B : ℝ≥0 := t + 1
  let F : ℝ≥0 → ℝ := (Ioc 0 B).indicator g
  have htB : t < B := lt_add_of_pos_right t (by norm_num)
  obtain ⟨hS, heq⟩ :=
    Kyprianou.Ch02.truncatedCumulativeAtomicSeriesAgreementV1 g B (hs B)
  have hlim :=
    AvramDividend.Classical.avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right
      F hS t
  have hnear : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, s < B :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ s : ℝ≥0 in 𝓝 t, s < B from isOpen_Iio.mem_nhds htB)
  have hident : (fun s : ℝ≥0 => ∑' u : ℝ≥0,
      if 0 < u ∧ u ≤ s then F u else 0) =ᶠ[𝓝[>] t]
      (fun s : ℝ≥0 => ∑' u : Ioc (0 : ℝ≥0) s, g u) :=
    hnear.mono (fun s hs => heq s hs.le)
  rw [← show insert t (Ioi t) = Ici t by ext s; simp [le_iff_eq_or_lt, eq_comm]]
  apply continuousWithinAt_insert.mpr
  change Tendsto (fun s : ℝ≥0 => ∑' u : Ioc (0 : ℝ≥0) s, g u)
    (𝓝[>] t) (𝓝 (∑' u : Ioc (0 : ℝ≥0) t, g u))
  rw [← heq t htB.le]
  exact hlim.congr' hident
