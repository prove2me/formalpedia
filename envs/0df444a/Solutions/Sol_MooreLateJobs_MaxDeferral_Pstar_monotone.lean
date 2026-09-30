-- Prove2me | solution 1 for MooreLateJobs.MaxDeferral.Pstar_monotone
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:03:39.495309+00:00
-- url     : https://prove2.me/submissions/4e826516-4bc3-47ea-aa96-f2500a887076

import Definitions.Def_MooreLateJobs_MaxDeferral_Pstar
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
open MooreLateJobs.MaxDeferral

private theorem pstar_le_level (f : ℝ → ℝ) (hc : Continuous f) (hm : Monotone f)
    (y s : ℝ) (hs : 0 ≤ s) (hys : y < f s) : Pstar f y ≤ (s : EReal) := by
  classical
  by_cases hy : ∃ u, 0 ≤ u ∧ f u=y
  · have hbound (u : ℝ) (hu : 0 ≤ u ∧ f u=y) : u ≤ s := by
      by_contra h
      have hh := hm (le_of_lt (lt_of_not_ge h))
      rw [hu.2] at hh
      linarith
    have hb : BddAbove {u | 0 ≤ u ∧ f u=y} := ⟨s,hbound⟩
    simp only [Pstar,if_pos hy,if_pos hb,EReal.coe_le_coe_iff]
    exact csSup_le hy hbound
  · have hall : ∀ u, 0 ≤ u → y < f u := by
      intro u hu
      by_contra h
      have huy : f u ≤ y := le_of_not_gt h
      have hus : u ≤ s := by
        by_contra hn
        have hh := hm (le_of_lt (lt_of_not_ge hn))
        linarith
      obtain ⟨w,hw,hew⟩ := intermediate_value_Icc hus hc.continuousOn ⟨huy,hys.le⟩
      exact hy ⟨w,le_trans hu hw.1,hew⟩
    simp only [Pstar,if_neg hy,if_pos hall]
    exact_mod_cast hs

theorem solution (f : ℝ → ℝ) (hcont : Continuous f) (hmono : Monotone f) :
    Monotone (Pstar f) := by
  classical
  intro y z hyz
  rcases eq_or_lt_of_le hyz with rfl|hyz
  · exact le_rfl
  by_cases hz : ∃ s, 0 ≤ s ∧ f s=z
  · by_cases hb : BddAbove {s | 0 ≤ s ∧ f s=z}
    · obtain ⟨s,hs,hsz⟩ := hz
      have hp := pstar_le_level f hcont hmono y s hs (by simpa [hsz] using hyz)
      apply hp.trans
      simp only [Pstar,if_pos (show ∃ u, 0 ≤ u ∧ f u=z from ⟨s,hs,hsz⟩),if_pos hb,EReal.coe_le_coe_iff]
      exact le_csSup hb ⟨hs,hsz⟩
    · simp only [Pstar,if_pos hz,if_neg hb]
      exact le_top
  · by_cases hall : ∀ s, 0 ≤ s → z < f s
    · have hally : ∀ s, 0 ≤ s → y < f s := fun s hs => hyz.trans (hall s hs)
      have hny : ¬∃ s, 0 ≤ s ∧ f s=y := by
        rintro ⟨s,hs,hsy⟩
        have := hally s hs
        linarith
      simp only [Pstar,if_neg hz,if_neg hny,if_pos hall,if_pos hally,le_refl]
    · simp only [Pstar,if_neg hz,if_neg hall]
      exact le_top
