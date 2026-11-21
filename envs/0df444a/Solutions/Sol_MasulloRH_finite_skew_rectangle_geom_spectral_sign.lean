-- Prove2me | solution 1 for MasulloRH.finite_skew_rectangle_geom_spectral_sign
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T05:01:58.123324+00:00
-- url     : https://prove2.me/submissions/f656f935-343e-4dda-9a1d-27cc1fb6bd5b

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set

theorem solution {G : Type*} [Group G] [MeasurableSpace G]
    (L : G → ℝ) (hL : ∀ u v, L (u*v⁻¹) = L u - L v)
    (δ : ℝ) (hδ : 0 < δ) (φ : G → ℂ) (hφ : ∀ u, L u < δ → φ u = 0)
    (μ : Measure (G × G)) (geom spec : G × G → ℂ)
    (hk : ∀ᵐ p ∂μ, geom p = φ (p.1*p.2⁻¹) - spec p) :
    (∃ R : ℝ, 0 < R ∧ R+R < δ) ∧
    ∀ (r s : ℝ), 0 ≤ r → 0 ≤ s → r+s < δ →
    ∀ (x y : G), L x = L y → ∀ (U V : Set G), MeasurableSet U → MeasurableSet V →
      (∀ u ∈ U, |L u-L x| ≤ r) → (∀ v ∈ V, |L v-L y| ≤ s) →
      ∀ w : G × G → ℂ, IntegrableOn (fun p => w p * spec p) (U ×ˢ V) μ →
        IntegrableOn (fun p => w p * geom p) (U ×ˢ V) μ ∧
        (∫ p in U ×ˢ V, w p * geom p ∂μ) = -(∫ p in U ×ˢ V, w p * spec p ∂μ) := by
  refine ⟨⟨δ/3, by linarith, by linarith⟩, ?_⟩
  intro r s _ _ hrs x y hxy U V hU hV hUr hVs w hint
  have he : (fun p => w p * geom p) =ᵐ[μ.restrict (U ×ˢ V)] fun p => -(w p * spec p) := by
    filter_upwards [ae_restrict_of_ae hk, ae_restrict_mem (hU.prod hV)] with p hp hpUV
    have hu := (abs_le.mp (hUr p.1 hpUV.1)).2
    have hv := (abs_le.mp (hVs p.2 hpUV.2)).1
    have hsmall : L (p.1*p.2⁻¹) < δ := by rw [hL]; linarith
    simp [hp,hφ _ hsmall]
  exact ⟨hint.neg.congr he.symm, (integral_congr_ae he).trans (integral_neg _)⟩
