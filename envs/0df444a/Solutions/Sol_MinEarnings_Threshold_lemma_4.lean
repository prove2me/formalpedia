-- Prove2me | solution 1 for MinEarnings.Threshold.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:37:25.848984+00:00
-- url     : https://prove2.me/submissions/0a59d22a-f61f-4747-9e1f-646a759e98fa

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

set_option autoImplicit false
open MinEarnings.Threshold

theorem solution (D S H : ℝ → ℝ) (pStar wStar M : ℝ)
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (hM : 0 < M) (w z : ℕ → ℝ) (t : ℕ)
    (hzt : 0 < z t ∧ z t = w t * util D S (w t) (z t))
    (hwt : wStar ≤ w t) :
    M / util D S (w t) (z t) ≤ w (t + 1) ↔
      M * w t / H (revenue D (w t)) ≤ w (t + 1) := by
  obtain ⟨hz0, hzeq⟩ := hzt
  have hw0 : 0 ≤ w t := le_trans hA.wStar_nonneg hwt
  have hwpos : 0 < w t := by
    rcases hw0.eq_or_lt with h | h
    · exfalso; rw [← h] at hzeq; simp at hzeq; linarith
    · exact h
  have hSz : 0 < S (z t) := hA.S_pos _ hz0
  have hDw : 0 < D (w t) := hA.D_pos _ hw0
  have hR : 0 < revenue D (w t) := mul_pos hwpos hDw
  obtain ⟨hHpos, hHc⟩ := hH _ hR
  -- util = z / w
  have hutil : util D S (w t) (z t) = z t / w t := by
    field_simp
    linarith [hzeq]
  -- z = H(R(w))
  have hmin : min (D (w t)) (S (z t)) = D (w t) := by
    by_contra hne
    have hlt : S (z t) < D (w t) := by
      rcases le_total (D (w t)) (S (z t)) with h | h
      · exact absurd (min_eq_left h) hne
      · rcases h.eq_or_lt with h' | h'
        · exfalso; apply hne; rw [h', min_self]
        · exact h'
    have hmin' : min (D (w t)) (S (z t)) = S (z t) := min_eq_right hlt.le
    have hu : util D S (w t) (z t) = 1 := by
      unfold util quantity; rw [hmin']; exact div_self hSz.ne'
    rw [hu, mul_one] at hzeq
    -- z = w, so S w < D w, contradicting w ≥ w*
    have hDle : D (w t) ≤ D wStar :=
      hA.D_strictAntiOn.antitoneOn (Set.mem_Ici.mpr hA.wStar_nonneg) (Set.mem_Ici.mpr hw0) hwt
    have hSle : S wStar ≤ S (w t) :=
      hA.S_strictMonoOn.monotoneOn (Set.mem_Ici.mpr hA.wStar_nonneg) (Set.mem_Ici.mpr hw0) hwt
    rw [← hzeq] at hlt
    rw [hA.cross] at hDle
    rw [hzeq] at hlt
    linarith
  have hzH : z t = H (revenue D (w t)) := by
    have hc : z t * S (z t) = revenue D (w t) := by
      have : util D S (w t) (z t) = D (w t) / S (z t) := by
        unfold util quantity; rw [hmin]
      rw [this] at hzeq
      unfold revenue
      field_simp at hzeq ⊢
      linarith
    have hc' : cost S (H (revenue D (w t))) = revenue D (w t) := hHc
    unfold cost at hc'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : S (z t) < S (H (revenue D (w t))) :=
        hA.S_strictMonoOn (Set.mem_Ici.mpr hz0.le) (Set.mem_Ici.mpr hHpos.le) hlt
      nlinarith
    · have : S (H (revenue D (w t))) < S (z t) :=
        hA.S_strictMonoOn (Set.mem_Ici.mpr hHpos.le) (Set.mem_Ici.mpr hz0.le) hgt
      nlinarith
  rw [hutil, hzH]
  have : M / (H (revenue D (w t)) / w t) = M * w t / H (revenue D (w t)) := by
    field_simp
  rw [this]
