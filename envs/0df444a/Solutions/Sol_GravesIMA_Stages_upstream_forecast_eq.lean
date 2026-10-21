-- Prove2me | solution 1 for GravesIMA.Stages.upstream_forecast_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:46:42.99159+00:00
-- url     : https://prove2.me/submissions/78660455-3770-47d6-9b63-0164435e12ed

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

set_option autoImplicit false
open GravesIMA.Stages

lemma gis_err {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) : d t - F t = e t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  induction t, ht using Int.le_induction with
  | base => rw [h1, h3]; ring
  | succ t ht ih =>
    have h2' := h2 (t + 1) (by omega)
    simp only [add_sub_cancel_right] at h2'
    have hd : d t = F t + e t := by linarith
    rw [h2', h4 t ht, hd]; ring

lemma gis_Fstep {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) : F (t + 1) = F t + a * e t := by
  have := gis_err h t ht
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [h4 t ht]
  have hd : d t = F t + e t := by linarith
  rw [hd]; ring

lemma gis_Ico_succ (m : ℤ → ℝ) (s : ℤ) (hs : 1 ≤ s) :
    ∑ j ∈ Finset.Ico (1 : ℤ) (s + 1), m j = ∑ j ∈ Finset.Ico (1 : ℤ) s, m j + m s := by
  have : Finset.Ico (1 : ℤ) (s + 1) = insert s (Finset.Ico (1 : ℤ) s) := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [this, Finset.sum_insert (by simp), add_comm]

lemma gis_d {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) : d t = e t + a * ∑ j ∈ Finset.Ico (1 : ℤ) t, e j + μ := by
  have h1 := h.1
  have h2 := h.2.1
  induction t, ht using Int.le_induction with
  | base => rw [h1]; simp; ring
  | succ t ht ih =>
    have h2' := h2 (t + 1) (by omega)
    simp only [add_sub_cancel_right] at h2'
    rw [h2', ih, gis_Ico_succ e t ht]; ring

lemma gis_q {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) :
    q t = (1 + (L : ℝ) * a) * e t + a * ∑ j ∈ Finset.Ico (1 : ℤ) t, e j + μ := by
  have hq := h.2.2.2.2.2.1 t ht
  have hF := gis_Fstep h t ht
  rw [hq, gis_d h t ht, hF]; ring

lemma gis_F {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) : F (t + 1) = a * ∑ j ∈ Finset.Icc (1 : ℤ) t, e j + μ := by
  have h3 := h.2.2.1
  induction t, ht using Int.le_induction with
  | base => rw [gis_Fstep h 1 le_rfl, h3]; simp; ring
  | succ t ht ih =>
    rw [gis_Fstep h (t + 1) (by omega), ih]
    have : Finset.Icc (1 : ℤ) (t + 1) = insert (t + 1) (Finset.Icc (1 : ℤ) t) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [this, Finset.sum_insert (by simp)]; ring

/-- prefix sums of masked shocks -/
noncomputable def gisP (m : ℤ → ℝ) (s : ℤ) : ℝ := ∑ j ∈ Finset.Ico (1 : ℤ) s, m j

lemma gisP_succ (m : ℤ → ℝ) (hm : ∀ s, s ≤ 0 → m s = 0) (s : ℤ) :
    gisP m (s + 1) = gisP m s + m s := by
  rcases le_or_gt 1 s with hs | hs
  · exact gis_Ico_succ m s hs
  · have h0 : m s = 0 := hm s (by omega)
    have e1 : Finset.Ico (1 : ℤ) (s + 1) = ∅ := by
      ext j; simp only [Finset.mem_Ico]; simp; omega
    have e2 : Finset.Ico (1 : ℤ) s = ∅ := by
      ext j; simp only [Finset.mem_Ico]; simp; omega
    simp [gisP, e1, e2, h0]

lemma gisP_of_le (m : ℤ → ℝ) (s : ℤ) (hs : s ≤ 1) : gisP m s = 0 := by
  have e2 : Finset.Ico (1 : ℤ) s = ∅ := by
    ext j; simp only [Finset.mem_Ico]; simp; omega
  simp [gisP, e2]

/-- telescoping identity for the weighted window sums -/
lemma gis_tele (c a : ℝ) (m : ℤ → ℝ) (hm : ∀ s, s ≤ 0 → m s = 0) (t : ℤ) (K : ℕ) :
    ∑ i ∈ Finset.range K, m (t - i) * (c + i * a) - ∑ i ∈ Finset.range K, m (t - 1 - i) * (c + i * a)
      = (c * m t + a * gisP m t) - ((c + K * a) * m (t - K) + a * gisP m (t - K)) := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hP := gisP_succ m hm (t - n - 1)
    have e : t - n - 1 + 1 = t - n := by ring
    rw [e] at hP
    have e2 : t - 1 - (n : ℤ) = t - n - 1 := by ring
    have e3 : t - ((n + 1 : ℕ) : ℤ) = t - n - 1 := by push_cast; ring
    rw [e2, e3]
    push_cast
    rw [hP] at ih
    linarith

lemma gis_masked_zero (e : ℤ → ℝ) : ∀ s : ℤ, s ≤ 0 → (fun s : ℤ => if 1 ≤ s then e s else 0) s = 0 := by
  intro s hs; simp only; rw [if_neg (by omega)]

lemma gisP_eq (e : ℤ → ℝ) (s : ℤ) :
    gisP (fun s : ℤ => if 1 ≤ s then e s else 0) s = ∑ j ∈ Finset.Ico (1 : ℤ) s, e j := by
  unfold gisP
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Ico] at hj
  simp [hj.1]

lemma gis_q_all {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x) (s : ℤ) :
    q s = (1 + (L : ℝ) * a) * (fun s : ℤ => if 1 ≤ s then e s else 0) s
      + a * gisP (fun s : ℤ => if 1 ≤ s then e s else 0) s + μ := by
  rcases le_or_gt 1 s with hs | hs
  · rw [gis_q h s hs, gisP_eq]; simp [hs]
  · have h5 := h.2.2.2.2.1 s (by omega)
    rw [h5, gisP_of_le _ s (by omega)]; simp [not_le.mpr hs]

lemma gis_G {μ α : ℝ} (hα0 : 0 ≤ α) {L K : ℕ} {ε d F q x G p y : ℤ → ℝ}
    (h : IsTwoStage μ α L K ε d F q x G p y) (t : ℤ) (ht : 1 ≤ t) : G t = F t := by
  obtain ⟨hs, hu⟩ := h
  obtain ⟨u1, u2, u3, u4, u5⟩ := hu
  have hpos : (1 + (L : ℝ) * α) ≠ 0 := by positivity
  have hbeta : upBeta α L * (1 + (L : ℝ) * α) = α := by
    unfold upBeta; field_simp
  induction t, ht using Int.le_induction with
  | base => rw [u1, hs.2.2.1]
  | succ t ht ih =>
    have hq : q t = F t + (1 + (L : ℝ) * α) * ε t := by
      have e1 := hs.2.2.2.2.2.1 t ht
      have e2 := gis_err hs t ht
      have e3 := gis_Fstep hs t ht
      rw [e1, e3]; linarith
    rw [u2 t ht, gis_Fstep hs t ht, ih, hq]
    linear_combination (ε t) * hbeta

lemma gis_p_all {μ α : ℝ} (hα0 : 0 ≤ α) {L K : ℕ} {ε d F q x G p y : ℤ → ℝ}
    (h : IsTwoStage μ α L K ε d F q x G p y) (s : ℤ) :
    p s = (1 + ((L : ℝ) + K) * α) * (fun s : ℤ => if 1 ≤ s then ε s else 0) s
      + α * gisP (fun s : ℤ => if 1 ≤ s then ε s else 0) s + μ := by
  rcases le_or_gt 1 s with hs | hs
  · have hp := h.2.2.2.2.1 s hs
    have hG1 := gis_G hα0 h s hs
    have hG2 := gis_G hα0 h (s + 1) (by omega)
    have hF := gis_Fstep h.1 s hs
    have hq := gis_q h.1 s hs
    rw [hp, hG2, hG1, hF, hq, gisP_eq]
    simp [hs]; ring
  · have h5 := h.2.2.2.1 s (by omega)
    rw [h5, gisP_of_le _ s (by omega)]; simp [not_le.mpr hs]

theorem solution (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L K : ℕ)
    (ε d F q x G p y : ℤ → ℝ) (h : IsTwoStage μ α L K ε d F q x G p y) (t : ℤ) (ht : 1 ≤ t) :
    q t = G t + (1 + (L : ℝ) * α) * ε t ∧ q t = F t + (1 + (L : ℝ) * α) * ε t ∧ G t = F t := by
  have hG := gis_G hα0 h t ht
  have hq : q t = F t + (1 + (L : ℝ) * α) * ε t := by
    have e1 := h.1.2.2.2.2.2.1 t ht
    have e2 := gis_err h.1 t ht
    have e3 := gis_Fstep h.1 t ht
    rw [e1, e3]; linarith
  exact ⟨by rw [hG]; exact hq, hq, hG⟩
