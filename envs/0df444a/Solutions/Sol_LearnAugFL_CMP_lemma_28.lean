-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_28
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:44:04.872916+00:00
-- url     : https://prove2.me/submissions/a977a1ad-7eda-4cd2-b4ab-4e8405b65122

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

open LearnAugFL.CMP

theorem solution (p₁ p₂ p₃ : Pt) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    dist (p₁ + ε • (p₂ - p₁)) p₃ + dist (p₂ + ε • (p₁ - p₂)) p₃ ≤ dist p₁ p₃ + dist p₂ p₃ ∧
    (¬ Collinear ℝ ({p₁, p₂, p₃} : Set Pt) →
      dist (p₁ + ε • (p₂ - p₁)) p₃ + dist (p₂ + ε • (p₁ - p₂)) p₃ < dist p₁ p₃ + dist p₂ p₃) := by
  have hεc : 0 < 1 - ε := sub_pos.mpr hε1
  have hmove (x y : Pt) : x + ε • (y - x) - p₃ =
      (1 - ε) • (x - p₃) + ε • (y - p₃) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  have hweak (x y : Pt) : dist (x + ε • (y - x)) p₃ ≤
      (1 - ε) * dist x p₃ + ε * dist y p₃ := by
    simp only [dist_eq_norm, hmove]
    calc
      _ ≤ ‖(1 - ε) • (x - p₃)‖ + ‖ε • (y - p₃)‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul,
        Real.norm_of_nonneg hεc.le, Real.norm_of_nonneg hε0.le]
  constructor
  · have ha := hweak p₁ p₂
    have hb := hweak p₂ p₁
    nlinarith
  · intro hcol
    have hnot : ¬ SameRay ℝ (p₁ - p₃) (p₂ - p₃) := by
      intro hray
      obtain ⟨r, _, hr⟩ := hray.exists_nonneg_left (sub_ne_zero.mpr h13)
      apply hcol
      apply (collinear_iff_of_mem (by simp : p₃ ∈ ({p₁, p₂, p₃} : Set Pt))).2
      refine ⟨p₁ - p₃, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hp | hp | hp
      · subst p
        exact ⟨1, by simp⟩
      · subst p
        refine ⟨r, ?_⟩
        change p₂ = r • (p₁ - p₃) + p₃
        rw [hr]
        simp
      · subst p
        exact ⟨0, by simp⟩
    have hscaled : ¬ SameRay ℝ ((1 - ε) • (p₁ - p₃)) (ε • (p₂ - p₃)) := by
      intro hray
      apply hnot
      have h := (hray.pos_smul_left (inv_pos.mpr hεc)).pos_smul_right (inv_pos.mpr hε0)
      simpa only [smul_smul, inv_mul_cancel₀ hεc.ne', inv_mul_cancel₀ hε0.ne', one_smul] using h
    have hstrict : dist (p₁ + ε • (p₂ - p₁)) p₃ <
        (1 - ε) * dist p₁ p₃ + ε * dist p₂ p₃ := by
      simpa only [dist_eq_norm, hmove, norm_smul, Real.norm_of_nonneg hεc.le,
        Real.norm_of_nonneg hε0.le] using norm_add_lt_of_not_sameRay hscaled
    have hb := hweak p₂ p₁
    nlinarith
