-- Prove2me | solution 1 for MinEarnings.Threshold.loose_threshold_gt_wStar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:22:33.030384+00:00
-- url     : https://prove2.me/submissions/68807590-bab6-4b61-858f-117f295aa6e0

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

theorem solution (D S H : ℝ → ℝ) (pStar wStar : ℝ)
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (hloose : wStar < pStar) :
    wStar < H (revenue D pStar) := by
  have hRpos : 0 < revenue D pStar := by
    unfold revenue
    exact mul_pos (lt_of_le_of_lt hA.wStar_nonneg hloose) (hA.D_pos _ (hA.pStar_nonneg))
  obtain ⟨hHpos, hHc⟩ := hH _ hRpos
  by_contra hcon
  push Not at hcon
  have h1 : cost S (H (revenue D pStar)) ≤ cost S wStar :=
    Z_cost_mono D S pStar wStar hA _ _ hHpos hcon
  rw [hHc, Z_cost_wStar D S pStar wStar hA] at h1
  have h2 : revenue D wStar < revenue D pStar :=
    hA.revenue_strictMonoOn ⟨hA.wStar_nonneg, hloose.le⟩ ⟨hA.pStar_nonneg, le_rfl⟩ hloose
  linarith
