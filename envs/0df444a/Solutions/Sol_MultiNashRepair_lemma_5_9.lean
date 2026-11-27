-- Prove2me | solution 1 for MultiNashRepair.lemma_5_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:05:45.864158+00:00
-- url     : https://prove2.me/submissions/5bc18bd6-9623-4fc4-9ad7-019453c228eb

import Mathlib
import Definitions.Def_MultiNashRepair_ScalarCertificate

open MultiNashRepair

theorem MNR59_kf_ge_iff {f H v : ℝ} (hf : 0 < f) (hH : 0 ≤ H) :
    v ≤ Kf f H ↔ v * (f * (f + H)) ≤ (1 + H) * (f + (2 * f - 1) * H) := by
  unfold Kf
  rw [le_div_iff₀ (by positivity)]

theorem MNR59_caseA {f : ℝ} (hf : 0 < f) (h3 : 3 * f ^ 2 ≤ 1) :
    IsLeast (Kf f '' Set.Icc 0 f) (1 + f) := by
  refine ⟨⟨f, ⟨hf.le, le_rfl⟩, ?_⟩, ?_⟩
  · unfold Kf
    rw [div_eq_iff (by positivity)]
    ring
  · rintro _ ⟨H, ⟨h0, h1⟩, rfl⟩
    rw [MNR59_kf_ge_iff hf h0]
    have key : (1 + H) * (f + (2*f-1)*H) - (1+f)*(f*(f+H))
        = (f - H) * (-((2*f-1)*H + f^2 + f - 1)) := by ring
    have hb : (2*f-1)*H + f^2 + f - 1 ≤ 0 := by
      rcases le_total (2*f-1) 0 with ha | ha
      · have := mul_nonpos_of_nonpos_of_nonneg ha h0
        nlinarith
      · have := mul_le_mul_of_nonneg_left h1 ha
        nlinarith
    have := mul_nonneg (sub_nonneg.mpr h1) (neg_nonneg.mpr hb)
    linarith

theorem MNR59_caseC {f : ℝ} (hf2 : 2 / 3 ≤ f) :
    IsLeast (Kf f '' Set.Icc 0 f) (1 / f) := by
  have hf : 0 < f := by linarith
  refine ⟨⟨0, ⟨le_rfl, hf.le⟩, ?_⟩, ?_⟩
  · unfold Kf
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rintro _ ⟨H, ⟨h0, h1⟩, rfl⟩
    rw [MNR59_kf_ge_iff hf h0]
    have e : 1 / f * (f * (f + H)) = f + H := by field_simp
    rw [e]
    have := mul_nonneg h0 (by nlinarith : (0:ℝ) ≤ (2*f-1)*H + 3*f - 2)
    nlinarith

theorem MNR59_caseB {f : ℝ} (h3 : 1 ≤ 3 * f ^ 2) (hf0 : 0 < f) (hfu : f ≤ 2 / 3) :
    IsLeast (Kf f '' Set.Icc 0 f)
      (5 - 4 * f - 1 / f + 2 * (1 - f) * Real.sqrt (4 - 2 / f)) := by
  have hf : 0 < f := hf0
  have ha : 0 < 2 * f - 1 := by nlinarith
  have h2f : 2 / f ≤ 4 := by rw [div_le_iff₀ hf]; linarith
  set r := Real.sqrt (4 - 2 / f) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 4 - 2 / f := Real.sq_sqrt (by linarith)
  have hfr : f * r ^ 2 = 4 * f - 2 := by rw [hr2]; field_simp
  set V := 5 - 4 * f - 1 / f + 2 * (1 - f) * r with hV
  have hVf : V * f = 5 * f - 4 * f ^ 2 - 1 + 2 * f * (1 - f) * r := by
    rw [hV]; field_simp
  have hX : ∀ H : ℝ, (1 + H) * (f + (2 * f - 1) * H) - V * (f * (f + H))
      = (2*f-1) * (f+H)^2 - 2 * (1-f) * f * r * (f+H) + 2 * f * (1-f)^2 := by
    intro H
    have : V * (f * (f + H)) = (V * f) * (f + H) := by ring
    rw [this, hVf]; ring
  have haX : ∀ y : ℝ, (2*f-1) * ((2*f-1) * y^2 - 2 * (1-f) * f * r * y + 2 * f * (1-f)^2)
      = ((2*f-1) * y - (1-f) * f * r) ^ 2 := by
    intro y
    linear_combination (-(1-f)^2 * f) * hfr
  have hXnn : ∀ y : ℝ, 0 ≤ (2*f-1) * y^2 - 2 * (1-f) * f * r * y + 2 * f * (1-f)^2 := by
    intro y
    have h := haX y
    have : 0 ≤ (2*f-1) * ((2*f-1) * y^2 - 2 * (1-f) * f * r * y + 2 * f * (1-f)^2) := by
      rw [h]; positivity
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg ha hneg
    linarith
  -- the minimizer
  have hfr' : f * ((1 - f) * r) ^ 2 = (1 - f) ^ 2 * (4 * f - 2) := by
    rw [← hfr]; ring
  have hlo : 2 * f - 1 ≤ (1 - f) * r := by
    have h1 : f * (2 * f - 1) ^ 2 ≤ f * ((1 - f) * r) ^ 2 := by
      rw [hfr']
      nlinarith [mul_nonneg ha.le (by linarith : (0:ℝ) ≤ 2 - 3 * f)]
    have h2 : (2 * f - 1) ^ 2 ≤ ((1 - f) * r) ^ 2 := le_of_mul_le_mul_left h1 hf
    have h3' : 0 ≤ (1 - f) * r := mul_nonneg (by linarith) hr0
    nlinarith
  have hhi : (1 - f) * r ≤ 2 * (2 * f - 1) := by
    have h1 : f * ((1 - f) * r) ^ 2 ≤ f * (2 * (2 * f - 1)) ^ 2 := by
      rw [hfr']
      nlinarith [mul_nonneg ha.le (by linarith : (0:ℝ) ≤ 3 * f ^ 2 - 1)]
    have h2 : ((1 - f) * r) ^ 2 ≤ (2 * (2 * f - 1)) ^ 2 := le_of_mul_le_mul_left h1 hf
    nlinarith
  set Hs := (1 - f) * f * r / (2 * f - 1) - f with hHs
  have hys : f + Hs = (1 - f) * f * r / (2 * f - 1) := by rw [hHs]; ring
  have hHs0 : 0 ≤ Hs := by
    rw [hHs, sub_nonneg, le_div_iff₀ ha]
    nlinarith
  have hHs1 : Hs ≤ f := by
    rw [hHs, sub_le_iff_le_add, div_le_iff₀ ha]
    nlinarith
  refine ⟨⟨Hs, ⟨hHs0, hHs1⟩, ?_⟩, ?_⟩
  · have hz : (2*f-1) * (f + Hs) - (1-f) * f * r = 0 := by
      rw [hys]; field_simp; ring
    have h0 := haX (f + Hs)
    rw [hz] at h0
    have hX0 : (2*f-1) * (f+Hs)^2 - 2 * (1-f) * f * r * (f+Hs) + 2 * f * (1-f)^2 = 0 := by
      rcases mul_eq_zero.mp (h0.trans (by ring)) with h | h
      · linarith
      · exact h
    have := hX Hs
    unfold Kf
    rw [div_eq_iff (by positivity)]
    linarith
  · rintro _ ⟨H, ⟨h0, h1⟩, rfl⟩
    rw [MNR59_kf_ge_iff hf h0]
    have := hX H
    have := hXnn (f + H)
    linarith

theorem solution :
    (∀ f : ℝ, 0 < f → f < 1 → IsLeast (Kf f '' Set.Icc 0 f) (U f)) ∧
    (∀ f : ℝ, 0 < f → f ≤ 1 / Real.sqrt 3 → U f = 1 + f) ∧
    (∀ f : ℝ, 1 / Real.sqrt 3 ≤ f → f ≤ 2 / 3 →
      U f = 5 - 4 * f - 1 / f + 2 * (1 - f) * Real.sqrt (4 - 2 / f)) ∧
    (∀ f : ℝ, 2 / 3 ≤ f → f < 1 → U f = 1 / f) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := by positivity
  have hA : ∀ f : ℝ, 0 < f → f ≤ 1 / Real.sqrt 3 → 3 * f ^ 2 ≤ 1 := by
    intro f hf h
    rw [le_div_iff₀ hs3p] at h
    nlinarith
  have hB : ∀ f : ℝ, 1 / Real.sqrt 3 ≤ f → 1 ≤ 3 * f ^ 2 ∧ 0 < f := by
    intro f h
    have hf : 0 < f := lt_of_lt_of_le (by positivity) h
    rw [div_le_iff₀ hs3p] at h
    exact ⟨by nlinarith, hf⟩
  have UA : ∀ f : ℝ, 0 < f → f ≤ 1 / Real.sqrt 3 → U f = 1 + f := fun f hf h =>
    (MNR59_caseA hf (hA f hf h)).csInf_eq
  have UB : ∀ f : ℝ, 1 / Real.sqrt 3 ≤ f → f ≤ 2 / 3 →
      U f = 5 - 4 * f - 1 / f + 2 * (1 - f) * Real.sqrt (4 - 2 / f) := fun f h h' =>
    (MNR59_caseB (hB f h).1 (hB f h).2 h').csInf_eq
  have UC : ∀ f : ℝ, 2 / 3 ≤ f → f < 1 → U f = 1 / f := fun f h _ =>
    (MNR59_caseC h).csInf_eq
  refine ⟨?_, UA, UB, UC⟩
  intro f hf hf1
  rcases le_total f (1 / Real.sqrt 3) with h | h
  · rw [UA f hf h]; exact MNR59_caseA hf (hA f hf h)
  · rcases le_total f (2 / 3) with h' | h'
    · rw [UB f h h']; exact MNR59_caseB (hB f h).1 (hB f h).2 h'
    · rw [UC f h' hf1]; exact MNR59_caseC h'
