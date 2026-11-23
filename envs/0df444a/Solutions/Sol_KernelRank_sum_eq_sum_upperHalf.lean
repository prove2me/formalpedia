-- Prove2me | solution 1 for KernelRank.sum_eq_sum_upperHalf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:25.47916+00:00
-- url     : https://prove2.me/submissions/37ffaf83-82e3-4071-b550-3bf4fc4361fe

import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_Representation
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero



set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (V : Finset ℂ) (hV : ∀ μ ∈ V, starRingEnd ℂ μ ∈ V) (f : ℂ → ℝ) :
    ∑ μ ∈ V, f μ = ∑ μ ∈ V.filter (fun μ => 0 ≤ μ.im),
      pairWeight μ * (f μ + f (starRingEnd ℂ μ)) := by
  classical
  have key : ∀ F : ℂ → ℝ, ∑ μ ∈ V, F (starRingEnd ℂ μ) = ∑ μ ∈ V, F μ := fun F =>
    Finset.sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ) hV hV (fun μ _ => Complex.conj_conj μ)
      (fun μ _ => Complex.conj_conj μ) (fun _ _ => rfl)
  let h : ℂ → ℝ := fun μ =>
    if 0 ≤ μ.im then pairWeight μ * (f μ + f (starRingEnd ℂ μ)) else 0
  have hpt : ∀ μ, h μ + h (starRingEnd ℂ μ) = f μ + f (starRingEnd ℂ μ) := by
    intro μ
    rcases lt_trichotomy μ.im 0 with hlt | heq | hgt
    · have h1 : ¬ 0 ≤ μ.im := not_le.mpr hlt
      have h2 : 0 ≤ (starRingEnd ℂ μ).im := by rw [Complex.conj_im]; linarith
      have h3 : (starRingEnd ℂ μ).im ≠ 0 := by rw [Complex.conj_im]; linarith
      simp only [h, h1, h2, h3, pairWeight, Complex.conj_conj, ↓reduceIte]
      ring
    · have hc : starRingEnd ℂ μ = μ := Complex.conj_eq_iff_im.mpr heq
      simp only [h, hc, heq, le_refl, pairWeight, ↓reduceIte]
      ring
    · have h1 : ¬ 0 ≤ (starRingEnd ℂ μ).im := by rw [Complex.conj_im]; linarith
      simp only [h, h1, hgt.le, hgt.ne', pairWeight, ↓reduceIte]
      ring
  have hsum : ∑ μ ∈ V, (h μ + h (starRingEnd ℂ μ)) = ∑ μ ∈ V, h μ + ∑ μ ∈ V, h μ := by
    rw [Finset.sum_add_distrib, key h]
  have hsum' : ∑ μ ∈ V, (f μ + f (starRingEnd ℂ μ)) = ∑ μ ∈ V, f μ + ∑ μ ∈ V, f μ := by
    rw [Finset.sum_add_distrib, key f]
  simp only [hpt] at hsum
  rw [Finset.sum_filter]
  change ∑ μ ∈ V, f μ = ∑ μ ∈ V, h μ
  linarith
end KernelRank
