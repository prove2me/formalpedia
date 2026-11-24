-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:34:10.162501+00:00
-- url     : https://prove2.me/submissions/dcf956dc-fed4-4c74-a500-7908e241e9f7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransformStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussFou_gauss_eq_prod
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussFou_neg_inv_im_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussFou_sqrt_norm_det
import Theorems.Thm_GlobalTheory_T_real_gaussian_fourier_transform


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussFou
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.GaussFou
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → Integrable (gauss B ρ P τ) ∧ ‖cG B ρ P τ‖ = (∏ w, ‖τ w‖ ^ M)⁻¹ ∧ cG B ρ P τ * cG B ρ P (fun w => -(τ w)⁻¹) = 1 ∧ ∀ y : InfinitePlace F → ι → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x, gauss B ρ P τ x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) y := by
  intro F _ _ ι _ _ M B ρ P hQ τ hτ
  obtain ⟨hF, hcard, hsym, hdet, hρ, hP, hrel⟩ := hQ
  have hdetw : ∀ w, (B.map (ρ w)).det ≠ 0 := fun w => by
    have : (B.map (ρ w)).det = ρ w B.det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact (map_ne_zero (ρ w)).2 hdet
  have one := fun w => GlobalTheory.T.real_gaussian_fourier_transform ι (B.map (ρ w)) (P w) (hsym.map _) (hdetw w) (hP w) (hrel w)
  choose c hc using one
  have hfou : ∀ σ : InfinitePlace F → ℂ, (∀ w, 0 < (σ w).im) → ∀ y : InfinitePlace F → ι → ℝ,
      ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x, gauss B ρ P σ x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) =
      ∏ w, (c w (σ w) * g1 (B.map (ρ w)) (P w) (-(σ w)⁻¹) (y w)) := by
    intro σ hσ y
    have hint : ∀ x : InfinitePlace F → ι → ℝ, gauss B ρ P σ x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) =
        ∏ w, (g1 (B.map (ρ w)) (P w) (σ w) (x w) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))) := by
      intro x
      rw [gauss_eq_prod, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, Finset.prod_mul_distrib]
    simp_rw [hint]
    rw [integral_fintype_prod_volume_eq_prod
      (f := fun w (x : ι → ℝ) => g1 (B.map (ρ w)) (P w) (σ w) x *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))),
      sqrt_norm_det B ρ hF hρ, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact (hc w (σ w) (hσ w)).2.2.2 (y w)
  have hcG : ∀ σ : InfinitePlace F → ℂ, (∀ w, 0 < (σ w).im) → cG B ρ P σ = ∏ w, c w (σ w) := by
    intro σ hσ
    have h0 := hfou σ hσ 0
    simpa [cG, g1] using h0
  have hσ' : ∀ w, 0 < (-(τ w)⁻¹).im := fun w => neg_inv_im_pos (hτ w)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : gauss B ρ P τ = fun x => ∏ w, g1 (B.map (ρ w)) (P w) (τ w) (x w) :=
      funext fun x => gauss_eq_prod B ρ P τ x
    rw [this]
    exact Integrable.fintype_prod (f := fun w => g1 (B.map (ρ w)) (P w) (τ w))
      fun w => (hc w (τ w) (hτ w)).2.2.1
  · rw [hcG τ hτ, norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(hc w (τ w) (hτ w)).1, hcard, pow_mul, Real.sq_sqrt (norm_nonneg _)]
  · rw [hcG τ hτ, hcG _ hσ', ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun w _ => (hc w (τ w) (hτ w)).2.1
  · intro y
    rw [hfou τ hτ y, hcG τ hτ, gauss_eq_prod, Finset.prod_mul_distrib]
end GlobalTheory.CompanionTheory.SW.GaussFou
