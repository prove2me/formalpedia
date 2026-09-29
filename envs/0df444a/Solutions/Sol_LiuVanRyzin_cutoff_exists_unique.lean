-- Prove2me | solution 1 for LiuVanRyzin.cutoff_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:57:28.579272+00:00
-- url     : https://prove2.me/submissions/8202eea3-c76a-49bf-bf03-3dc8295a9299

import Mathlib
import Definitions.Def_LiuVanRyzin_Model

namespace LiuVanRyzin

lemma aux_lvr_inc {u : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ici 0) u) {a d h : ℝ} (ha : 0 ≤ a)
    (hd : 0 ≤ d) (hh : 0 ≤ h) : u (a + d + h) + u a ≤ u (a + h) + u (a + d) := by
  rcases eq_or_lt_of_le (add_nonneg hd hh) with hs | hs
  · have hd0 : d = 0 := by linarith
    have hh0 : h = 0 := by linarith
    subst hd0; subst hh0; simp
  · have hxm : a ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr ha
    have hym : a + d + h ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (by linarith)
    have hsum1 : d / (d + h) + h / (d + h) = 1 := by field_simp
    have hsum2 : h / (d + h) + d / (d + h) = 1 := by rw [add_comm]; exact hsum1
    have h1 := hc.2 hxm hym (div_nonneg hd hs.le) (div_nonneg hh hs.le) hsum1
    have h2 := hc.2 hxm hym (div_nonneg hh hs.le) (div_nonneg hd hs.le) hsum2
    have e1 : d / (d + h) * a + h / (d + h) * (a + d + h) = a + h := by field_simp; ring
    have e2 : h / (d + h) * a + d / (d + h) * (a + d + h) = a + d := by field_simp; ring
    simp only [smul_eq_mul] at h1 h2
    rw [e1] at h1
    rw [e2] at h2
    have key : (d / (d + h) + h / (d + h)) * (u a + u (a + d + h)) ≤ u (a + h) + u (a + d) := by
      nlinarith [h1, h2]
    rw [hsum1] at key
    linarith

end LiuVanRyzin

open LiuVanRyzin

theorem solution (u : ℝ → ℝ) (hu : IsCustomerUtility u) (p₁ p₂ : ℝ)
    (hp : p₂ < p₁) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    p₁ ≤ cutoff u p₁ p₂ q ∧
      (∀ v : ℝ, cutoff u p₁ p₂ q < v → buysEarly u p₁ p₂ q v) ∧
      (∀ v : ℝ, v < cutoff u p₁ p₂ q → ¬ buysEarly u p₁ p₂ q v) ∧
      (∀ t : ℝ, p₁ ≤ t → (∀ v : ℝ, t < v → buysEarly u p₁ p₂ q v) →
        (∀ v : ℝ, v < t → ¬ buysEarly u p₁ p₂ q v) → t = cutoff u p₁ p₂ q) := by
  obtain ⟨hmono, hconc, _hcont, _hdiff, hu0⟩ := hu
  set S := {v : ℝ | buysEarly u p₁ p₂ q v} with hS
  have hcut : cutoff u p₁ p₂ q = sInf S := rfl
  rw [hcut]
  have hc : 0 < p₁ - p₂ := by linarith
  have hup : ∀ v w, buysEarly u p₁ p₂ q v → v ≤ w → buysEarly u p₁ p₂ q w := by
    rintro v w ⟨hv1, hv2⟩ hvw
    refine ⟨le_trans hv1 hvw, ?_⟩
    have key := aux_lvr_inc hconc (a := v - p₁) (d := p₁ - p₂) (h := w - v)
      (by linarith) (by linarith) (by linarith)
    have e1 : v - p₁ + (p₁ - p₂) + (w - v) = w - p₂ := by ring
    have e2 : v - p₁ + (w - v) = w - p₁ := by ring
    have e3 : v - p₁ + (p₁ - p₂) = v - p₂ := by ring
    rw [e1, e2, e3] at key
    have hmon : u (v - p₁) ≤ u (w - p₁) :=
      hmono.monotoneOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith))
        (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left key hq0,
      mul_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hmon)]
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hlt : ∀ y, 0 ≤ y → u y < q * u (y + (p₁ - p₂)) := by
      intro y hy
      have hns : y + p₁ ∉ S := by rw [hemp]; exact Set.notMem_empty _
      simp only [hS, Set.mem_ofPred_eq, buysEarly, not_and, not_le] at hns
      have h' := hns (by linarith)
      have e1 : y + p₁ - p₂ = y + (p₁ - p₂) := by ring
      have e2 : y + p₁ - p₁ = y := by ring
      rw [e1, e2] at h'
      exact h'
    have hsub : ∀ y, 0 ≤ y → u (y + (p₁ - p₂)) ≤ u y + u (p₁ - p₂) := by
      intro y hy
      have h' := aux_lvr_inc hconc (a := 0) (d := y) (h := p₁ - p₂) le_rfl hy hc.le
      simp only [zero_add, hu0] at h'
      linarith
    have hbdd : BddAbove (u '' Set.Ici 0) := by
      refine ⟨q * u (p₁ - p₂) / (1 - q), ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hlt y hy
      have h2 := hsub y hy
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left h2 hq0]
    have hL : ∀ y, 0 ≤ y → u y ≤ sSup (u '' Set.Ici 0) :=
      fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
    have hLq : sSup (u '' Set.Ici 0) ≤ q * sSup (u '' Set.Ici 0) := by
      apply csSup_le (Set.nonempty_Ici.image u)
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hlt y hy
      have h2 := hL (y + (p₁ - p₂)) (by linarith [Set.mem_Ici.mp hy])
      nlinarith
    have hu1 : 0 < u 1 := by
      have h' := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_lt_one
      rwa [hu0] at h'
    have h1 := hL 1 zero_le_one
    nlinarith
  have hbdd : BddBelow S := ⟨p₁, fun v hv => hv.1⟩
  refine ⟨le_csInf hne (fun v hv => hv.1), ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hwS, hwv⟩ := exists_lt_of_csInf_lt hne hv
    exact hup w v hwS hwv.le
  · intro v hv hb
    have := csInf_le hbdd hb
    linarith
  · intro t _ht hgt hlt
    apply le_antisymm
    · apply le_csInf hne
      intro v hv
      by_contra h
      push Not at h
      exact hlt v h hv
    · by_contra h
      push Not at h
      have hm := csInf_le hbdd (hgt ((t + sInf S) / 2) (by linarith))
      linarith
