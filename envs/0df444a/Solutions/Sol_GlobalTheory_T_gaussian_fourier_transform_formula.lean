-- Prove2me | solution 1 for GlobalTheory.T.gaussian_fourier_transform_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:06.069177+00:00
-- url     : https://prove2.me/submissions/73485c7a-035f-4b16-b79e-cb6ad2131fc5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussFlat_gauss_fourier_flat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ y : ι × InfinitePlace F → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (DM B ρ *ᵥ y) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) (cur y) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat | exact GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat <;> assumption)
end _root_.GlobalTheory.T
