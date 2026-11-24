-- Prove2me | solution 1 for GlobalTheory.T.archimedean_gaussian_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:47:18.047415+00:00
-- url     : https://prove2.me/submissions/2bf69a54-49c1-4825-88a5-0ac40a858c58

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourierStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussFou_gauss_fourier


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → Integrable (gauss B ρ P τ) ∧ ‖cG B ρ P τ‖ = (∏ w, ‖τ w‖ ^ M)⁻¹ ∧ cG B ρ P τ * cG B ρ P (fun w => -(τ w)⁻¹) = 1 ∧ ∀ y : InfinitePlace F → ι → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x, gauss B ρ P τ x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, x w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) y := by
  first | exact @GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier | exact GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier | (intros; apply GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier <;> assumption)
end _root_.GlobalTheory.T
