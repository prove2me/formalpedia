-- Prove2me | solution 1 for NewMinimalStandardModel.singlet_quartic_landau_pole
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:49:15.600713+00:00
-- url     : https://prove2.me/submissions/807a3319-c0e0-4d17-aa4f-59fbdb295677

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

open NewMinimalStandardModel in
theorem solution (h k : ℝ → ℝ) (t₀ T : ℝ)
    (hODE : ∀ t ∈ Set.Ico t₀ T,
      HasDerivAt h ((3 * h t ^ 2 + 12 * k t ^ 2) / (4 * Real.pi) ^ 2) t)
    (h₀ : 0 < h t₀) :
    T ≤ t₀ + 16 * Real.pi ^ 2 / (3 * h t₀) := by
  by_contra hT
  rw [not_le] at hT
  set a : ℝ := 3 / (4 * Real.pi) ^ 2 with ha
  have hpi : 0 < (4 * Real.pi) ^ 2 := by positivity
  have hapos : 0 < a := by positivity
  have hc : 0 < 16 * Real.pi ^ 2 / (3 * h t₀) := by positivity
  have hD : Convex ℝ (Set.Ico t₀ T) := convex_Ico _ _
  have hcont : ContinuousOn h (Set.Ico t₀ T) :=
    fun t ht => (hODE t ht).continuousAt.continuousWithinAt
  have hint : interior (Set.Ico t₀ T) = Set.Ioo t₀ T := interior_Ico
  have hmono : MonotoneOn h (Set.Ico t₀ T) := by
    apply monotoneOn_of_deriv_nonneg hD hcont
    · intro t ht
      rw [hint] at ht
      exact (hODE t (Set.Ioo_subset_Ico_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [hint] at ht
      rw [(hODE t (Set.Ioo_subset_Ico_self ht)).deriv]
      positivity
  have ht₀D : t₀ ∈ Set.Ico t₀ T := ⟨le_refl _, by linarith⟩
  have hpos : ∀ t ∈ Set.Ico t₀ T, 0 < h t :=
    fun t ht => lt_of_lt_of_le h₀ (hmono ht₀D ht ht.1)
  have hgd : ∀ t ∈ Set.Ico t₀ T, HasDerivAt (fun y => (h y)⁻¹ + a * y)
      (-((3 * h t ^ 2 + 12 * k t ^ 2) / (4 * Real.pi) ^ 2) / (h t) ^ 2 + a * 1) t := by
    intro t ht
    exact ((hODE t ht).inv (hpos t ht).ne').add ((hasDerivAt_id' t).const_mul a)
  have hanti : AntitoneOn (fun y => (h y)⁻¹ + a * y) (Set.Ico t₀ T) := by
    apply antitoneOn_of_deriv_nonpos hD
    · exact fun t ht => (hgd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [hint] at ht
      exact (hgd t (Set.Ioo_subset_Ico_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [hint] at ht
      have ht' := Set.Ioo_subset_Ico_self ht
      rw [(hgd t ht').deriv]
      have hh := hpos t ht'
      have hh2 : 0 < h t ^ 2 := by positivity
      have key : a * h t ^ 2 ≤ (3 * h t ^ 2 + 12 * k t ^ 2) / (4 * Real.pi) ^ 2 := by
        rw [ha, div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hpi.le
        nlinarith [sq_nonneg (k t)]
      have : a ≤ (3 * h t ^ 2 + 12 * k t ^ 2) / (4 * Real.pi) ^ 2 / h t ^ 2 := by
        rw [le_div_iff₀ hh2]; exact key
      rw [neg_div]
      linarith
  set s := t₀ + 16 * Real.pi ^ 2 / (3 * h t₀) with hs
  have hsD : s ∈ Set.Ico t₀ T := ⟨by linarith, hT⟩
  have hle := hanti ht₀D hsD (by linarith)
  simp only at hle
  have hcalc : a * (s - t₀) = (h t₀)⁻¹ := by
    rw [hs, ha]
    field_simp
    ring
  have hspos := hpos s hsD
  have : (h s)⁻¹ ≤ 0 := by nlinarith
  have : 0 < (h s)⁻¹ := inv_pos.mpr hspos
  linarith
