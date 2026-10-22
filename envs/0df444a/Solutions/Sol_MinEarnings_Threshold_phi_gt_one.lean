-- Prove2me | solution 1 for MinEarnings.Threshold.phi_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:22:59.058237+00:00
-- url     : https://prove2.me/submissions/acc6c638-810c-48b7-a97d-fa0623a8b223

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

set_option autoImplicit false
open MinEarnings.Threshold

lemma Z_cost_mono (D S : ℝ → ℝ) (pStar wStar : ℝ) (hA : Assumptions D S pStar wStar)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : cost S a ≤ cost S b := by
  unfold cost
  have hSab : S a ≤ S b :=
    hA.S_strictMonoOn.monotoneOn (Set.mem_Ici.mpr ha.le) (Set.mem_Ici.mpr (ha.le.trans hab)) hab
  exact mul_le_mul hab hSab (hA.S_pos a ha).le (ha.le.trans hab)

lemma Z_cost_wStar (D S : ℝ → ℝ) (pStar wStar : ℝ) (hA : Assumptions D S pStar wStar) :
    cost S wStar = revenue D wStar := by
  unfold cost revenue
  rw [← hA.cross]

theorem solution (D S H : ℝ → ℝ) (pStar wStar M : ℝ)
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (htight : pStar ≤ wStar) (hMw : wStar < M) :
    1 < M / H (revenue D M) := by
  have hM0 : 0 < M := lt_of_le_of_lt hA.wStar_nonneg hMw
  have hRpos : 0 < revenue D M := by
    unfold revenue
    exact mul_pos hM0 (hA.D_pos _ hM0.le)
  obtain ⟨hHpos, hHc⟩ := hH _ hRpos
  have hRM : revenue D M < revenue D wStar :=
    hA.revenue_strictAntiOn (Set.mem_Ici.mpr htight) (Set.mem_Ici.mpr (htight.trans hMw.le)) hMw
  have hlt : H (revenue D M) < wStar := by
    by_contra hcon
    push Not at hcon
    have h1 : cost S wStar ≤ cost S (H (revenue D M)) := by
      rcases hA.wStar_nonneg.eq_or_lt with h0 | h0
      · -- wStar = 0 : then revenue D wStar = 0 < revenue D M contradicts hRM
        have : revenue D wStar = 0 := by unfold revenue; rw [← h0]; ring
        linarith
      · exact Z_cost_mono D S pStar wStar hA _ _ h0 hcon
    rw [hHc, Z_cost_wStar D S pStar wStar hA] at h1
    linarith
  rw [lt_div_iff₀ hHpos]
  linarith
