-- Prove2me | solution 1 for HarksKlimm.Consistency.local_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:03:42.94504+00:00
-- url     : https://prove2.me/submissions/61ec7674-f9a5-486b-9dcf-9babc8150709

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_IsMonotonic

open scoped NNReal
open HarksKlimm.Consistency

theorem g79i_A (c : ℝ≥0 → ℝ) (hc : Continuous c)
    (hL : ∀ x : ℝ≥0, 0 < x → c 0 < c x →
        ∃ ε : ℝ≥0, 0 < ε ∧ ∀ y : ℝ≥0, x < y → y < x + ε → c x ≤ c y)
    (u : ℝ≥0) (hu : 0 < u) (hcu : c 0 < c u) (b : ℝ≥0) (hb : u ≤ b) : c u ≤ c b := by
  set s : Set ℝ≥0 := {t | c u ≤ c t}
  have hs : IsClosed (s ∩ Set.Icc u b) := (isClosed_le continuous_const hc).inter isClosed_Icc
  have hsub := hs.Icc_subset_of_forall_exists_gt (show u ∈ s from le_refl (c u)) (by
    intro x hx y hy
    have hx0 : 0 < x := lt_of_lt_of_le hu hx.2.1
    have hcx : c u ≤ c x := hx.1
    obtain ⟨ε, hε, hloc⟩ := hL x hx0 (lt_of_lt_of_le hcu hcx)
    set z := min (x + ε / 2) y
    have hxz : x < z := lt_min (lt_add_of_pos_right _ (half_pos hε)) hy
    have hzε : z < x + ε := lt_of_le_of_lt (min_le_left _ _)
      ((add_lt_add_iff_left x).mpr (half_lt_self hε))
    exact ⟨z, hcx.trans (hloc z hxz hzε), hxz, min_le_right _ _⟩)
  exact hsub ⟨hb, le_rfl⟩

theorem solution (c : ℝ≥0 → ℝ) (hc : Continuous c) :
    IsMonotonic c ↔
      (∀ x : ℝ≥0, 0 < x → c 0 < c x →
        ∃ ε : ℝ≥0, 0 < ε ∧ ∀ y : ℝ≥0, x < y → y < x + ε → c x ≤ c y) ∧
      (∀ x : ℝ≥0, 0 < x → c x < c 0 →
        ∃ ε : ℝ≥0, 0 < ε ∧ ∀ y : ℝ≥0, x < y → y < x + ε → c y ≤ c x) := by
  constructor
  · rintro (hm | hm)
    · refine ⟨fun x _ _ => ⟨1, one_pos, fun y hxy _ => hm hxy.le⟩, fun x hx hlt => ?_⟩
      exact absurd (hm (by positivity : (0:ℝ≥0) ≤ x)) (not_le.mpr hlt)
    · refine ⟨fun x hx hlt => ?_, fun x _ _ => ⟨1, one_pos, fun y hxy _ => hm hxy.le⟩⟩
      exact absurd (hm (by positivity : (0:ℝ≥0) ≤ x)) (not_le.mpr hlt)
  · rintro ⟨hL, hR⟩
    have P2 : ∀ u t, u < t → c 0 < c u → c u ≤ c t := by
      intro u t hut hu
      rcases eq_or_ne u 0 with h | h
      · rw [h] at hu; exact absurd hu (lt_irrefl _)
      · exact g79i_A c hc hL u (pos_iff_ne_zero.mpr h) hu t hut.le
    have P1 : ∀ u t, u < t → c u < c 0 → c t ≤ c u := by
      intro u t hut hu
      rcases eq_or_ne u 0 with h | h
      · rw [h] at hu; exact absurd hu (lt_irrefl _)
      · have := g79i_A (fun z => -c z) hc.neg (fun x hx hlt => by
          obtain ⟨ε, hε, h'⟩ := hR x hx (by linarith)
          exact ⟨ε, hε, fun y h1 h2 => by have := h' y h1 h2; linarith⟩)
          u (pos_iff_ne_zero.mpr h) (by linarith) t hut.le
        linarith
    by_cases hup : ∀ t, c 0 ≤ c t
    · left
      intro a b hab
      rcases (hup a).lt_or_eq with h | h
      · rcases hab.lt_or_eq with h' | h'
        · exact P2 a b h' h
        · rw [h']
      · rw [← h]; exact hup b
    · push Not at hup
      obtain ⟨w, hw⟩ := hup
      have hdown : ∀ t, c t ≤ c 0 := by
        intro t; by_contra ht; push Not at ht
        rcases lt_trichotomy t w with h | h | h
        · have := P2 t w h ht; linarith
        · rw [h] at ht; linarith
        · have := P1 w t h hw; linarith
      right
      intro a b hab
      rcases (hdown a).lt_or_eq with h | h
      · rcases hab.lt_or_eq with h' | h'
        · exact P1 a b h' h
        · rw [h']
      · rw [h]; exact hdown b
