-- Prove2me | solution 1 for GlobalTheory.Published.landherr_of_landherrSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:03.4218+00:00
-- url     : https://prove2.me/submissions/e6e520f4-65ed-4727-8cc1-70c650dc7834

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__LandherrStIffLandherr_9fec213082f17e18
import Theorems.Thm_GlobalTheory_Published_LandherrSt_herm_mulVec
import Theorems.Thm_GlobalTheory_Published_LandherrSt_exists_gram_eq_sgn
import Theorems.Thm_GlobalTheory_Published_cc_ne_zero
import Theorems.Thm_GlobalTheory_Published_gram_eq
import Theorems.Thm_GlobalTheory_Published_herm_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.Published
namespace LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end LandherrSt
open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma cc_inv' {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z⁻¹ = (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc z)⁻¹ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact map_inv₀ _ _
namespace LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end LandherrSt
open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma one_map_cc {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} :
    (1 : Matrix (Fin r) (Fin r) E).map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc = 1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact Matrix.map_one _ (map_zero _) (map_one _)
end GlobalTheory.Published
end

set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open NumberField Matrix
open scoped nonZeroDivisors
namespace GlobalTheory.Published
namespace _root_.GlobalTheory.Published
theorem _root_.solution (H : _root_.GlobalTheory.Published.LandherrSt) :
    _root_.GlobalTheory.Published.Landherr := by
  intro E _ _ _ r G G' hG hG' hd hd' hcong hdet
  obtain ⟨x, hx⟩ := hdet
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hx
    exact div_ne_zero hd hd' hx
  have hsig : ∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧
      (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) := by
    intro τ
    obtain ⟨p, Q, hQ, hgram⟩ :=
      _root_.GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn hG hd τ
    obtain ⟨R, hR, hR'⟩ := hcong τ
    have hRu : IsUnit R.det := isUnit_iff_ne_zero.2 hR
    refine ⟨p, ⟨Q, hQ, hgram⟩, R⁻¹ * Q, ?_, ?_⟩
    · rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero hR) hQ
    · have h1 : (R⁻¹)ᵀ * Rᵀ = 1 := by
        rw [← transpose_mul, mul_nonsing_inv _ hRu, transpose_one]
      have h2 : R.map (starRingEnd ℂ) * (R⁻¹).map (starRingEnd ℂ) = 1 := by
        rw [← Matrix.map_mul, mul_nonsing_inv _ hRu, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [_root_.GlobalTheory.Published.gram_eq] at hgram ⊢
      rw [hR', transpose_mul, Matrix.map_mul, ← hgram]
      calc Qᵀ * (R⁻¹)ᵀ * (Rᵀ * G.map τ * R.map (starRingEnd ℂ)) *
            ((R⁻¹).map (starRingEnd ℂ) * Q.map (starRingEnd ℂ))
          = Qᵀ * ((R⁻¹)ᵀ * Rᵀ) * G.map τ * (R.map (starRingEnd ℂ) * (R⁻¹).map (starRingEnd ℂ)) *
            Q.map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
        _ = Qᵀ * G.map τ * Q.map (starRingEnd ℂ) := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
  have hdet' : G'.det = x⁻¹ * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc x⁻¹ * G.det := by
    rw [div_eq_iff hd'] at hx
    rw [cc_inv', hx]
    field_simp [hx0, _root_.GlobalTheory.Published.cc_ne_zero hx0]
  obtain ⟨γ, hγ⟩ := H E r G G' hG hG' hd hd' hsig ⟨x⁻¹, hdet'⟩
  · refine ⟨γ, ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero, ?_⟩
    ext a b
    have h := hγ (fun k => (1 : Matrix (Fin r) (Fin r) E) k a)
      (fun k => (1 : Matrix (Fin r) (Fin r) E) k b)
    rw [_root_.GlobalTheory.Published.LandherrSt.herm_mulVec,
      _root_.GlobalTheory.Published.herm_col, _root_.GlobalTheory.Published.herm_col,
      one_map_cc] at h
    simpa using h.symm
end _root_.GlobalTheory.Published
end GlobalTheory.Published
